module

public import CFSG.GH74.Uniqueness.ZStarSylow

public section

namespace CFSG.GH74.Uniqueness

open Subgroup
open scoped Pointwise

section ZNum

variable {X : Type*} [Group X]

@[expose] noncomputable def zNum (Z : Set X) (M : Subgroup X) : ℕ :=
  Nat.card ↥(Z ∩ (M : Set X))

theorem zNum_conjugate {Z : Set X} (hZ : IsInvariantInvolutionSet Z) (M : Subgroup X) (g : X) :
    zNum Z (conjugate M g) = zNum Z M := by
  have hZc : ∀ y ∈ Z, g * y * g⁻¹ ∈ Z := fun y hy => by
    have := hZ.2 y hy g⁻¹
    rwa [inv_inv] at this
  unfold zNum
  refine Nat.card_congr
    { toFun := fun y => ⟨g * (y : X) * g⁻¹, hZc _ y.2.1, mem_conjugate_iff.mp y.2.2⟩
      invFun := fun w => ⟨g⁻¹ * (w : X) * g, hZ.2 _ w.2.1 g, mem_conjugate_iff.mpr (by
        have e : g * (g⁻¹ * (w : X) * g) * g⁻¹ = (w : X) := by group
        rw [e]
        exact w.2.2)⟩
      left_inv := fun y => Subtype.ext (by simp only [mul_assoc]; group)
      right_inv := fun w => Subtype.ext (by simp only [mul_assoc]; group) }

end ZNum

section ThreeH

variable {X : Type*} [Group X] {Z : Set X}

theorem mem_set_mul_singleton_iff {A : Set X} {t s : X} : s ∈ A * {t} ↔ s * t⁻¹ ∈ A := by
  rw [Set.mul_singleton, Set.mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa using ha
  · intro hs
    exact ⟨s * t⁻¹, hs, by simp⟩

theorem mem_zCoset_iff_mem_invertedSet (hZ : IsInvariantInvolutionSet Z) {K : Subgroup X} {s : X}
    (hs : s ∈ Z) (hK : Odd (Nat.card K)) (hsK : s ∈ normalizer (K : Set X)) {v : X} :
    (v ∈ Z ∧ v * s⁻¹ ∈ K) ↔ ∃ x ∈ CFSG.OddInversion.invertedSet K s, v = x * s := by
  have hs2 : orderOf s = 2 := hZ.1 s hs
  obtain ⟨hset, hbij, -⟩ := CFSG.OddInversion.odd_inversion_coset_count hK hsK
    (CFSG.OddInversion.notMem_of_odd_card hK hs2) hs2
  constructor
  · rintro ⟨hvZ, hvK⟩
    obtain ⟨x, hx, hxv⟩ := hbij.surjOn (show v ∈ {w : X | w * s⁻¹ ∈ K ∧ orderOf w = 2} from
      ⟨hvK, hZ.1 v hvZ⟩)
    exact ⟨x, hx, hxv.symm⟩
  · rintro ⟨x, hx, rfl⟩
    have hmem := hbij.mapsTo hx
    have hm : x * s ∈ {w : X | ∃ d ∈ K, w = d⁻¹ * s * d} := by rw [← hset]; exact hmem
    obtain ⟨d, -, hd⟩ := hm
    exact ⟨by rw [hd]; exact hZ.2 s hs d, hmem.1⟩

theorem card_zCoset_eq_card_invertedSet (hZ : IsInvariantInvolutionSet Z) {K : Subgroup X}
    {s : X} (hs : s ∈ Z) (hK : Odd (Nat.card K)) (hsK : s ∈ normalizer (K : Set X)) :
    Nat.card {v : X // v ∈ Z ∧ v * s⁻¹ ∈ K} = Nat.card (CFSG.OddInversion.invertedSet K s) := by
  have key := fun v : X => mem_zCoset_iff_mem_invertedSet hZ hs hK hsK (v := v)
  refine Nat.card_congr
    { toFun := fun v => ⟨(v : X) * s⁻¹, ?_⟩
      invFun := fun x => ⟨(x : X) * s, ((key _).mpr ⟨x, x.2, rfl⟩).1, ?_⟩
      left_inv := fun v => Subtype.ext (by simp)
      right_inv := fun x => Subtype.ext (by simp) }
  · obtain ⟨x, hx, hxv⟩ := (key v).mp v.2
    have : (v : X) * s⁻¹ = x := by rw [hxv]; simp
    rw [this]
    exact hx
  · exact ((key _).mpr ⟨x, x.2, rfl⟩).2

end ThreeH

section Prop36

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

omit [Finite X] in
theorem mem_normalizer_inf_conjugate {t : X} (ht : t * t = 1) :
    t ∈ normalizer ((M ⊓ conjugate M t : Subgroup X) : Set X) := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact fun hx => mul_mul_inv_mem_inf_conjugate ht hx
  · intro hx
    have := mul_mul_inv_mem_inf_conjugate ht hx
    have e : t * (t * x * t⁻¹) * t⁻¹ = x := by
      calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t⁻¹ * t⁻¹) := by group
        _ = x := by rw [ht, hti, ht]; group
    rwa [e] at this

theorem IsProductDisconnected.exists_mul_centralizer_inf_conjugate
    (hZ : IsInvariantInvolutionSet Z) (h : IsProductDisconnected Z M) {t : X} (ht : t ∈ Z)
    (htM : t ∉ M) {d : X} (hd : d ∈ M ⊓ conjugate M t) :
    ∃ a ∈ pPrimeCoreIn (M ⊓ conjugate M t),
      ∃ c ∈ (M ⊓ conjugate M t) ⊓ centralizer ({t} : Set X), d = a * c := by
  have ht2 : t * t = 1 := hZ.mul_self_eq_one ht
  have hZs := h.isZStarIn_inf_conjugate_sup hZ ht htM
  exact exists_mul_centralizer_pPrimeCoreIn (hZ.1 t ht) (mem_normalizer_inf_conjugate ht2)
    (fun d hd => commutator_mem_pPrimeCoreIn hZs (mem_normalizer_inf_conjugate ht2) hd) hd

theorem IsProductDisconnected.mem_invertedSet_of_mem_zCoset (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {t s : X} (ht : t ∈ Z) (htM : t ∉ M) (hs : s ∈ Z)
    (hsM : s * t⁻¹ ∈ M) :
    s * t⁻¹ ∈ CFSG.OddInversion.invertedSet (pPrimeCoreIn (M ⊓ conjugate M t)) t := by
  have ht2 : t * t = 1 := hZ.mul_self_eq_one ht
  have hs2 : s * s = 1 := hZ.mul_self_eq_one hs
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  set x := s * t⁻¹ with hx
  have hxt : x * t = s := by rw [hx, mul_assoc, inv_mul_cancel, mul_one]
  have hsM' : s * t ∈ M := by rw [← hti]; exact hsM
  have hconj : t * x * t⁻¹ = x⁻¹ := by
    have h1 : (x * t) * (x * t) = 1 := by rw [hxt]; exact hs2
    have h2 : x * (t * x * t⁻¹) = 1 := by
      calc x * (t * x * t⁻¹) = (x * t) * (x * t) * (t⁻¹ * t⁻¹) := by group
        _ = 1 := by rw [h1, hti, ht2]; simp
    exact eq_inv_of_mul_eq_one_right h2
  have hxD : x ∈ M ⊓ conjugate M t :=
    Subgroup.mem_inf.mpr ⟨hsM, mem_conjugate_iff.mpr (by rw [hconj]; exact M.inv_mem hsM)⟩
  have hodd : Odd (orderOf x) := by
    have := h.odd_orderOf_mul hZ ht htM hs (Or.inr hsM')
    rwa [← hti] at this
  have hcomm := commutator_mem_pPrimeCoreIn (h.isZStarIn_inf_conjugate_sup hZ ht htM)
    (mem_normalizer_inf_conjugate ht2) hxD
  have e : x * t * x⁻¹ * t⁻¹ = x * x := by
    have h3 : t * x⁻¹ * t⁻¹ = x := by
      have := congrArg (fun y => y⁻¹) hconj
      simpa [mul_inv_rev, mul_assoc] using this
    calc x * t * x⁻¹ * t⁻¹ = x * (t * x⁻¹ * t⁻¹) := by group
      _ = x * x := by rw [h3]
  rw [e] at hcomm
  exact ⟨mem_of_mul_self_mem_of_odd_orderOf hodd hcomm, hconj⟩

theorem mem_zCoset_of_mem_invertedSet (hZ : IsInvariantInvolutionSet Z)
    {t x : X} (ht : t ∈ Z) (hx : x ∈ CFSG.OddInversion.invertedSet
      (pPrimeCoreIn (M ⊓ conjugate M t)) t) :
    x * t ∈ Z ∧ x ∈ M ⊓ conjugate M t := by
  have hK := odd_card_pPrimeCoreIn (M ⊓ conjugate M t)
  have ht2 := hZ.mul_self_eq_one ht
  have htK := mem_normalizer_pPrimeCoreIn (mem_normalizer_inf_conjugate (M := M) ht2)
  refine ⟨?_, pPrimeCoreIn_le _ hx.1⟩
  have := (mem_zCoset_iff_mem_invertedSet hZ ht hK htK (v := x * t)).mpr ⟨x, hx, rfl⟩
  exact this.1

theorem IsProductDisconnected.prop36a (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {t : X} (ht : t ∈ Z) (htM : t ∉ M) :
    Z ∩ ((M : Set X) * {t}) = Z ∩ (((M ⊓ conjugate M t : Subgroup X) : Set X) * {t}) ∧
      Z ∩ (((M ⊓ conjugate M t : Subgroup X) : Set X) * {t}) =
        CFSG.OddInversion.invertedSet (pPrimeCoreIn (M ⊓ conjugate M t)) t * {t} := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right (hZ.mul_self_eq_one ht)
  refine ⟨?_, ?_⟩
  · ext s
    simp only [Set.mem_inter_iff, mem_set_mul_singleton_iff, SetLike.mem_coe]
    constructor
    · rintro ⟨hsZ, hsM⟩
      exact ⟨hsZ, pPrimeCoreIn_le _ (h.mem_invertedSet_of_mem_zCoset hZ ht htM hsZ hsM).1⟩
    · rintro ⟨hsZ, hsD⟩
      exact ⟨hsZ, (Subgroup.mem_inf.mp hsD).1⟩
  · ext s
    simp only [Set.mem_inter_iff, mem_set_mul_singleton_iff, SetLike.mem_coe]
    constructor
    · rintro ⟨hsZ, hsD⟩
      exact h.mem_invertedSet_of_mem_zCoset hZ ht htM hsZ (Subgroup.mem_inf.mp hsD).1
    · intro hsI
      obtain ⟨hsZ, hsD⟩ := mem_zCoset_of_mem_invertedSet hZ ht hsI
      rw [inv_mul_cancel_right] at hsZ
      exact ⟨hsZ, hsD⟩

theorem IsProductDisconnected.exists_centralizer_mul_invertedSet (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {t z : X} (ht : t ∈ Z) (htM : t ∉ M) (hz : z ∈ Z)
    (hzM : z ∈ M) {g : X} (hg : g ∈ M) :
    ∃ c ∈ centralizer ({z} : Set X),
      ∃ x ∈ CFSG.OddInversion.invertedSet (pPrimeCoreIn (M ⊓ conjugate M t)) t, g = c * x := by
  have hgt : g * t ∉ M := fun hmem => htM (by
    have := M.mul_mem (M.inv_mem hg) hmem
    simpa using this)
  obtain ⟨s, ⟨hsZ, hsC⟩, -⟩ := h.existsUnique_mem_rightCoset hZ hz hzM hgt
  have hCM := h.centralizer_le_of_mem hz hzM
  have e : s * (g * t)⁻¹ = s * t⁻¹ * g⁻¹ := by group
  rw [e] at hsC
  have hsM : s * t⁻¹ ∈ M := by
    have h1 := M.mul_mem (hCM hsC) hg
    have e' : s * t⁻¹ * g⁻¹ * g = s * t⁻¹ := by group
    rwa [e'] at h1
  exact ⟨(s * t⁻¹ * g⁻¹)⁻¹, (centralizer ({z} : Set X)).inv_mem hsC, s * t⁻¹,
    h.mem_invertedSet_of_mem_zCoset hZ ht htM hsZ hsM, by group⟩

theorem IsProductDisconnected.eq_of_mem_invertedSet (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {t z : X} (ht : t ∈ Z) (htM : t ∉ M) (hz : z ∈ Z)
    (hzM : z ∈ M) {x y : X}
    (hx : x ∈ CFSG.OddInversion.invertedSet (pPrimeCoreIn (M ⊓ conjugate M t)) t)
    (hy : y ∈ CFSG.OddInversion.invertedSet (pPrimeCoreIn (M ⊓ conjugate M t)) t)
    (hxy : y * x⁻¹ ∈ centralizer ({z} : Set X)) : x = y := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right (hZ.mul_self_eq_one ht)
  obtain ⟨hxZ, hxD⟩ := mem_zCoset_of_mem_invertedSet hZ ht hx
  obtain ⟨hyZ, -⟩ := mem_zCoset_of_mem_invertedSet hZ ht hy
  have hxM : x ∈ M := (Subgroup.mem_inf.mp hxD).1
  have hxtM : x * t ∉ M := fun hmem => htM (by
    have := M.mul_mem (M.inv_mem hxM) hmem
    simpa using this)
  have hprod : (y * t) * (x * t) ∈ centralizer ({z} : Set X) := by
    have h1 : t * x * t⁻¹ = x⁻¹ := hx.2
    rw [hti] at h1
    have e : (y * t) * (x * t) = y * x⁻¹ := by
      calc y * t * (x * t) = y * (t * x * t) := by group
        _ = y * x⁻¹ := by rw [h1]
    rwa [e]
  exact (mul_right_cancel (h.eq_of_mul_mem_centralizer hZ hz hzM hyZ hxZ hxtM hprod)).symm

theorem IsProductDisconnected.prop36b (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {t z : X} (ht : t ∈ Z) (htM : t ∉ M) (hz : z ∈ Z)
    (hzM : z ∈ M) :
    ((centralizer ({z} : Set X) : Subgroup X) : Set X) *
        CFSG.OddInversion.invertedSet (pPrimeCoreIn (M ⊓ conjugate M t)) t = (M : Set X) ∧
      CFSG.OddInversion.invertedSet (pPrimeCoreIn (M ⊓ conjugate M t)) t *
        ((centralizer ({z} : Set X) : Subgroup X) : Set X) = (M : Set X) := by
  have hCM := h.centralizer_le_of_mem hz hzM
  have hIM : ∀ x ∈ CFSG.OddInversion.invertedSet (pPrimeCoreIn (M ⊓ conjugate M t)) t, x ∈ M :=
    fun x hx => (Subgroup.mem_inf.mp (pPrimeCoreIn_le _ hx.1)).1
  constructor
  · ext g
    rw [Set.mem_mul]
    constructor
    · rintro ⟨c, hc, x, hx, rfl⟩
      exact M.mul_mem (hCM hc) (hIM x hx)
    · intro hg
      obtain ⟨c, hc, x, hx, rfl⟩ := h.exists_centralizer_mul_invertedSet hZ ht htM hz hzM hg
      exact ⟨c, hc, x, hx, rfl⟩
  · ext g
    rw [Set.mem_mul]
    constructor
    · rintro ⟨x, hx, c, hc, rfl⟩
      exact M.mul_mem (hIM x hx) (hCM hc)
    · intro hg
      obtain ⟨c, hc, x, hx, hgcx⟩ :=
        h.exists_centralizer_mul_invertedSet hZ ht htM hz hzM (M.inv_mem hg)
      refine ⟨x⁻¹, CFSG.OddInversion.invertedSet_inv hx, c⁻¹,
        (centralizer ({z} : Set X)).inv_mem hc, ?_⟩
      rw [← mul_inv_rev, ← hgcx, inv_inv]

theorem IsProductDisconnected.prop36c (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {t : X} (ht : t ∈ Z) (htM : t ∉ M) :
    (∀ z ∈ Z ∩ (M : Set X), Set.BijOn (fun x => x⁻¹ * z * x)
      (CFSG.OddInversion.invertedSet (pPrimeCoreIn (M ⊓ conjugate M t)) t)
      (Z ∩ (M : Set X))) ∧
    ∀ y ∈ Z ∩ (M : Set X),
      ∀ x ∈ CFSG.OddInversion.invertedSet (pPrimeCoreIn (M ⊓ conjugate M t)) t,
        x * y = y * x → x = 1 := by
  have hIM : ∀ x ∈ CFSG.OddInversion.invertedSet (pPrimeCoreIn (M ⊓ conjugate M t)) t, x ∈ M :=
    fun x hx => (Subgroup.mem_inf.mp (pPrimeCoreIn_le _ hx.1)).1
  refine ⟨fun z hzZM => ?_, fun y hy x hx hxy => ?_⟩
  · obtain ⟨hz, hzM⟩ := hzZM
    refine ⟨fun x hx => ⟨hZ.2 z hz x, M.mul_mem (M.mul_mem (M.inv_mem (hIM x hx)) hzM)
      (hIM x hx)⟩, fun x hx y hy hxy => ?_, fun w hw => ?_⟩
    · refine h.eq_of_mem_invertedSet hZ ht htM hz hzM hx hy ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hxy' : x⁻¹ * z * x = y⁻¹ * z * y := hxy
      calc y * x⁻¹ * z = y * (x⁻¹ * z * x) * x⁻¹ := by group
        _ = y * (y⁻¹ * z * y) * x⁻¹ := by rw [hxy']
        _ = z * (y * x⁻¹) := by group
    · obtain ⟨m, hm, hmw⟩ := h.exists_conj_mem hZ hz hzM hw.1 hw.2
      obtain ⟨c, hc, x, hx, rfl⟩ := h.exists_centralizer_mul_invertedSet hZ ht htM hz hzM hm
      refine ⟨x, hx, ?_⟩
      have hc' : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hc
      have hcz : c⁻¹ * z * c = z := by rw [mul_assoc, ← hc']; group
      show x⁻¹ * z * x = w
      rw [← hmw]
      calc x⁻¹ * z * x = x⁻¹ * (c⁻¹ * z * c) * x := by rw [hcz]
        _ = (c * x)⁻¹ * z * (c * x) := by group
  · have h1 : (1 : X) ∈ CFSG.OddInversion.invertedSet (pPrimeCoreIn (M ⊓ conjugate M t)) t :=
      ⟨(pPrimeCoreIn (M ⊓ conjugate M t)).one_mem, by simp⟩
    have := h.eq_of_mem_invertedSet hZ ht htM hy.1 hy.2 h1 hx (by
      rw [Subgroup.mem_centralizer_singleton_iff]
      simpa using hxy)
    exact this.symm

theorem IsProductDisconnected.prop36d (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {t z : X} (ht : t ∈ Z) (htM : t ∉ M) (hz : z ∈ Z)
    (hzM : z ∈ M) :
    Nat.card (CFSG.OddInversion.invertedSet (pPrimeCoreIn (M ⊓ conjugate M t)) t) = zNum Z M ∧
      Nat.card (CFSG.OddInversion.invertedSet (pPrimeCoreIn (M ⊓ conjugate M t)) t) =
        (centralizer ({t} : Set X)).relIndex (pPrimeCoreIn (M ⊓ conjugate M t)) ∧
      (centralizer ({t} : Set X)).relIndex (M ⊓ conjugate M t) = zNum Z M ∧
      (centralizer ({z} : Set X)).relIndex (M ⊓ conjugate M t) = zNum Z M := by
  set D := M ⊓ conjugate M t with hD
  set K := pPrimeCoreIn D with hK
  have ht2 : t * t = 1 := hZ.mul_self_eq_one ht
  have hKodd : Odd (Nat.card K) := odd_card_pPrimeCoreIn D
  have htK : t ∈ normalizer (K : Set X) :=
    mem_normalizer_pPrimeCoreIn (mem_normalizer_inf_conjugate ht2)
  obtain ⟨hset, hbij, hcard⟩ := CFSG.OddInversion.odd_inversion_coset_count hKodd htK
    (CFSG.OddInversion.notMem_of_odd_card hKodd (hZ.1 t ht)) (hZ.1 t ht)
  have h1 : Nat.card (CFSG.OddInversion.invertedSet K t) = zNum Z M :=
    Nat.card_congr (Set.BijOn.equiv _ ((h.prop36c hZ ht htM).1 z ⟨hz, hzM⟩))
  refine ⟨h1, hcard, ?_, ?_⟩
  ·
    have hS : {y : X | ∃ d ∈ D, y = d⁻¹ * t * d} = {v : X | v * t⁻¹ ∈ K ∧ orderOf v = 2} := by
      rw [hset]
      ext y
      constructor
      · rintro ⟨d, hd, rfl⟩
        obtain ⟨a, ha, c, hc, hdc⟩ := h.exists_mul_centralizer_inf_conjugate hZ ht htM
          (D.inv_mem hd)
        have hc' : c * t = t * c := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc).2
        refine ⟨a⁻¹, K.inv_mem ha, ?_⟩
        have hd' : d = c⁻¹ * a⁻¹ := by
          have := congrArg (fun w => w⁻¹) hdc
          simpa [mul_inv_rev] using this
        rw [hd']
        calc (c⁻¹ * a⁻¹)⁻¹ * t * (c⁻¹ * a⁻¹) = a * (c * t * c⁻¹) * a⁻¹ := by group
          _ = a * t * a⁻¹ := by rw [hc']; group
          _ = (a⁻¹)⁻¹ * t * a⁻¹ := by rw [inv_inv]
      · rintro ⟨d, hd, rfl⟩
        exact ⟨d, pPrimeCoreIn_le D hd, rfl⟩
    have h2 := card_conj_orbit D t
    have h3 : Nat.card {y : X // ∃ d ∈ D, y = d⁻¹ * t * d} = Nat.card (CFSG.OddInversion.invertedSet K t) := by
      have : Nat.card ↥{y : X | ∃ d ∈ D, y = d⁻¹ * t * d} =
          Nat.card ↥{v : X | v * t⁻¹ ∈ K ∧ orderOf v = 2} := by rw [hS]
      exact this.trans (Nat.card_congr (Set.BijOn.equiv _ hbij)).symm
    rw [← h2, h3, h1]
  ·
    have hS : {y : X | ∃ d ∈ D, y = d⁻¹ * z * d} = Z ∩ (M : Set X) := by
      ext y
      constructor
      · rintro ⟨d, hd, rfl⟩
        exact ⟨hZ.2 z hz d, M.mul_mem (M.mul_mem (M.inv_mem (Subgroup.mem_inf.mp hd).1) hzM)
          (Subgroup.mem_inf.mp hd).1⟩
      · intro hy
        obtain ⟨x, hx, hxy⟩ := ((h.prop36c hZ ht htM).1 z ⟨hz, hzM⟩).surjOn hy
        exact ⟨x, pPrimeCoreIn_le D hx.1, hxy.symm⟩
    have h2 := card_conj_orbit D z
    rw [← h2]
    have : Nat.card ↥{y : X | ∃ d ∈ D, y = d⁻¹ * z * d} = Nat.card ↥(Z ∩ (M : Set X)) := by
      rw [hS]
    exact this

theorem IsProductDisconnected.odd_zNum (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {t z : X} (ht : t ∈ Z) (htM : t ∉ M) (hz : z ∈ Z)
    (hzM : z ∈ M) : Odd (zNum Z M) := by
  obtain ⟨h1, h2, -⟩ := h.prop36d hZ ht htM hz hzM
  rw [← h1, h2]
  exact Odd.of_dvd_nat (odd_card_pPrimeCoreIn _) (Subgroup.relIndex_dvd_card _ _)

theorem IsProductDisconnected.card_inter_centralizer_le_zNum (h : IsProductDisconnected Z M)
    {z : X} (hz : z ∈ Z) (hzM : z ∈ M) :
    Nat.card ↥(Z ∩ ((centralizer ({z} : Set X) : Subgroup X) : Set X)) ≤ zNum Z M :=
  Nat.card_mono (Set.toFinite _) (Set.inter_subset_inter_right Z
    (SetLike.coe_subset_coe.mpr (h.centralizer_le_of_mem hz hzM)))

theorem IsProductDisconnected.one_lt_card_inter_centralizer (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) (hgen : Subgroup.closure Z = ⊤)
    (hrank : 2 ≤ Open.twoRank X) {z : X} (hz : z ∈ Z) :
    1 < Nat.card ↥(Z ∩ ((centralizer ({z} : Set X) : Subgroup X) : Set X)) := by
  obtain ⟨y, hy, hne, hyz⟩ := h.exists_commuting_ne hZ hgen hrank hz
  have : Nontrivial ↥(Z ∩ ((centralizer ({z} : Set X) : Subgroup X) : Set X)) :=
    ⟨⟨⟨y, hy, Subgroup.mem_centralizer_singleton_iff.mpr hyz⟩,
      ⟨z, hz, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩,
      fun heq => hne (congrArg Subtype.val heq)⟩⟩
  exact Finite.one_lt_card_iff_nontrivial.mpr this

theorem IsProductDisconnected.prop36e (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) (hgen : Subgroup.closure Z = ⊤)
    (hrank : 2 ≤ Open.twoRank X) {t z : X} (ht : t ∈ Z) (htM : t ∉ M) (hz : z ∈ Z)
    (hzM : z ∈ M) :
    Odd (zNum Z M) ∧
      zNum Z M ≥ Nat.card ↥(Z ∩ ((centralizer ({z} : Set X) : Subgroup X) : Set X)) ∧
      Nat.card ↥(Z ∩ ((centralizer ({z} : Set X) : Subgroup X) : Set X)) > 1 :=
  ⟨h.odd_zNum hZ ht htM hz hzM, h.card_inter_centralizer_le_zNum hz hzM,
    h.one_lt_card_inter_centralizer hZ hgen hrank hz⟩

end Prop36

end CFSG.GH74.Uniqueness
