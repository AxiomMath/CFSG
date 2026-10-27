module

public import CFSG.GH74.QTGen4.Recog.G23.MSylow
public import CFSG.GH74.QTGen4.Recog.G23.MSylowB

public section

namespace CFSG.GH74.QTGen4.Recog.G23

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.G23Type
open scoped MatrixGroups

variable {G : Type*} [Group G]

open Classical in
noncomputable def thG {M : Subgroup G} (θ : ↥M →* SL(3, ZMod 2)) (g : G) : SL(3, ZMod 2) :=
  if h : g ∈ M then θ ⟨g, h⟩ else 1

theorem thG_of_mem {M : Subgroup G} (θ : ↥M →* SL(3, ZMod 2)) {g : G} (h : g ∈ M) :
    thG θ g = θ ⟨g, h⟩ := by
  simp [thG, h]

theorem thG_mul {M : Subgroup G} (θ : ↥M →* SL(3, ZMod 2)) {a b : G} (ha : a ∈ M)
    (hb : b ∈ M) : thG θ (a * b) = thG θ a * thG θ b := by
  rw [thG_of_mem θ (M.mul_mem ha hb), thG_of_mem θ ha, thG_of_mem θ hb, ← map_mul]
  rfl

theorem thG_inv {M : Subgroup G} (θ : ↥M →* SL(3, ZMod 2)) {a : G} (ha : a ∈ M) :
    thG θ a⁻¹ = (thG θ a)⁻¹ := by
  rw [thG_of_mem θ (M.inv_mem ha), thG_of_mem θ ha, ← map_inv]
  rfl

theorem thG_eq_one_iff {M V : Subgroup G} (θ : ↥M →* SL(3, ZMod 2))
    (hθk : θ.ker = V.subgroupOf M) {g : G} (hg : g ∈ M) :
    thG θ g = 1 ↔ g ∈ V := by
  rw [thG_of_mem θ hg, ← MonoidHom.mem_ker, hθk, Subgroup.mem_subgroupOf]

theorem thG_surj {M : Subgroup G} (θ : ↥M →* SL(3, ZMod 2)) (hθs : Function.Surjective θ)
    (u : SL(3, ZMod 2)) : ∃ m ∈ M, thG θ m = u := by
  obtain ⟨m, hm⟩ := hθs u
  exact ⟨m.1, m.2, by rw [thG_of_mem θ m.2]; simpa using hm⟩

theorem G23Two.comm_fitting {M : Subgroup G} (hM : G23Two M) {x y : G}
    (hx : x ∈ quasithinGenFitting M) (hy : y ∈ quasithinGenFitting M) : x * y = y * x :=
  congrArg Subtype.val (hM.elem.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem G23Two.sq_fitting {M : Subgroup G} (hM : G23Two M) {x : G}
    (hx : x ∈ quasithinGenFitting M) : x * x = 1 := by
  rw [← sq]
  exact hM.elem.2 x hx

theorem G23Two.conj_fitting {M : Subgroup G} {m : G} (hm : m ∈ M) {v : G}
    (hv : v ∈ quasithinGenFitting M) : m * v * m⁻¹ ∈ quasithinGenFitting M :=
  (Subgroup.mem_set_normalizer_iff.mp (le_normalizer_quasithinGenFitting M hm) v).mp hv

theorem G23Two.exists_conj_ne [Finite G] {M : Subgroup G} {t : G} (ht : t ∈ M)
    (htV : t ∉ quasithinGenFitting M) :
    ∃ v ∈ quasithinGenFitting M, t * v * t⁻¹ ≠ v := by
  by_contra h
  simp only [not_exists, not_and, ne_eq, not_not] at h
  apply htV
  have hc : t ∈ Subgroup.centralizer (quasithinGenFitting M : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have e : t * v * t⁻¹ = v := h v hv
    rw [mul_inv_eq_iff_eq_mul] at e
    exact e.symm
  exact centralizer_quasithinGenFitting_le M (Subgroup.mem_inf.mpr ⟨ht, hc⟩)

theorem G23Two.fitting_le_T [Finite G] {M T : Subgroup G} (hM : G23Two M) (hTM : T ≤ M)
    (hT2 : IsPGroup 2 T) (hTidx : ¬ 2 ∣ (T.subgroupOf M).index) :
    quasithinGenFitting M ≤ T := by
  have hVM : quasithinGenFitting M ≤ M := quasithinGenFitting_le M
  obtain ⟨θ, hθs, hθk⟩ := hM.quot
  have hT64 : Nat.card T = 64 := G23Two.card_sylow hM hTM hT2 hTidx
  have : ((quasithinGenFitting M).subgroupOf M).Normal := by
    rw [← hθk]
    infer_instance
  have hV'card : Nat.card ↥((quasithinGenFitting M).subgroupOf M) = 2 ^ 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVM).toEquiv, hM.card]
    norm_num
  have hV2 : IsPGroup 2 ((quasithinGenFitting M).subgroupOf M) :=
    IsPGroup.of_card hV'card
  have hT'card : Nat.card ↥(T.subgroupOf M) = 2 ^ 6 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTM).toEquiv, hT64]
    norm_num
  have hT'2 : IsPGroup 2 (T.subgroupOf M) := IsPGroup.of_card hT'card
  have hW : IsPGroup 2 (((quasithinGenFitting M).subgroupOf M ⊔ T.subgroupOf M : Subgroup ↥M)) :=
    IsPGroup.to_sup_of_normal_left hV2 hT'2
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hW
  have hdvd : Nat.card ↥(((quasithinGenFitting M).subgroupOf M ⊔ T.subgroupOf M : Subgroup ↥M)) ∣ 1344 := by
    rw [← G23Two.card_group hM]
    exact Subgroup.card_subgroup_dvd_card _
  rw [hk] at hdvd
  have hk6 : k ≤ 6 := by
    by_contra hk7
    have h1 : (2 : ℕ) ^ 7 ∣ 2 ^ k := Nat.pow_dvd_pow 2 (by omega)
    have h2 : (2 : ℕ) ^ 7 ∣ 1344 := h1.trans hdvd
    norm_num at h2
  have hle : Nat.card ↥(((quasithinGenFitting M).subgroupOf M ⊔ T.subgroupOf M : Subgroup ↥M)) ≤
      Nat.card ↥(T.subgroupOf M) := by
    rw [hk, hT'card]
    exact Nat.pow_le_pow_right (by norm_num) hk6
  have heq : T.subgroupOf M = (quasithinGenFitting M).subgroupOf M ⊔ T.subgroupOf M :=
    Subgroup.eq_of_le_of_card_ge le_sup_right hle
  intro g hg
  have hmem : (⟨g, hVM hg⟩ : ↥M) ∈ (quasithinGenFitting M).subgroupOf M :=
    Subgroup.mem_subgroupOf.mpr hg
  have hT' : (⟨g, hVM hg⟩ : ↥M) ∈ T.subgroupOf M := by
    rw [heq]
    exact Subgroup.mem_sup_left hmem
  exact Subgroup.mem_subgroupOf.mp hT'

theorem card_subtype_eq_sum_fibres {α β : Type*} [Finite α] [Fintype β] (p : α → Prop)
    (f : α → β) :
    Nat.card {a // p a} = ∑ b, Nat.card {a // p a ∧ f a = b} := by
  calc Nat.card {a // p a}
      = Nat.card (Σ b : β, {x : {a // p a} // f x.1 = b}) :=
        Nat.card_congr (Equiv.sigmaFiberEquiv (fun x : {a // p a} => f x.1)).symm
    _ = ∑ b, Nat.card {x : {a // p a} // f x.1 = b} := Nat.card_sigma
    _ = ∑ b, Nat.card {a // p a ∧ f a = b} := by
        refine Finset.sum_congr rfl fun b _ => ?_
        exact Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter p (fun a => f a = b))

theorem card_involution_subtype_eq (T : Subgroup G) :
    Nat.card {t : ↥T // orderOf t = 2} = Nat.card {g : G // g ∈ T ∧ g * g = 1 ∧ g ≠ 1} := by
  have key : ∀ t : ↥T, orderOf t = 2 ↔ ((t : G) * t = 1 ∧ (t : G) ≠ 1) := by
    intro t
    rw [orderOf_eq_prime_iff, sq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by simpa using congrArg Subtype.val h1,
        fun h => h2 (Subtype.ext (by simpa using h))⟩
    · rintro ⟨h1, h2⟩
      exact ⟨Subtype.ext (by simpa using h1), fun h => h2 (by simpa using congrArg Subtype.val h)⟩
  exact Nat.card_congr
    { toFun := fun t => ⟨t.1.1, t.1.2, ((key t.1).mp t.2).1, ((key t.1).mp t.2).2⟩
      invFun := fun g => ⟨⟨g.1, g.2.1⟩, (key ⟨g.1, g.2.1⟩).mpr ⟨g.2.2.1, g.2.2.2⟩⟩
      left_inv := fun t => Subtype.ext (Subtype.ext rfl)
      right_inv := fun g => Subtype.ext rfl }

theorem card_fibre_one [Finite G] {M T : Subgroup G} (hM : G23Two M) (hTM : T ≤ M)
    (hT2 : IsPGroup 2 T) (hTidx : ¬ 2 ∣ (T.subgroupOf M).index)
    (θ : ↥M →* SL(3, ZMod 2)) (hθk : θ.ker = (quasithinGenFitting M).subgroupOf M) :
    Nat.card {g : G // (g ∈ T ∧ g * g = 1 ∧ g ≠ 1) ∧ thG θ g = 1} = 7 := by
  have hVM : quasithinGenFitting M ≤ M := CFSG.Quasithin.quasithinGenFitting_le M
  have hVT : quasithinGenFitting M ≤ T := G23Two.fitting_le_T hM hTM hT2 hTidx
  have hequiv : ∀ g : G, ((g ∈ T ∧ g * g = 1 ∧ g ≠ 1) ∧ thG θ g = 1) ↔
      (g ∈ quasithinGenFitting M ∧ g ≠ 1) := by
    intro g
    constructor
    · rintro ⟨⟨hgT, _, hg1⟩, h1⟩
      exact ⟨(thG_eq_one_iff θ hθk (hTM hgT)).mp h1, hg1⟩
    · rintro ⟨hgV, hg1⟩
      exact ⟨⟨hVT hgV, G23Two.sq_fitting hM hgV, hg1⟩, (thG_eq_one_iff θ hθk (hVM hgV)).mpr hgV⟩
  classical
  rw [Nat.card_congr (Equiv.subtypeEquivRight hequiv)]
  rw [Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
    (fun g : G => g ∈ quasithinGenFitting M) (fun g : G => g ≠ 1)).symm]
  have hne : Nat.card {x : ↥(quasithinGenFitting M) // (x : G) ≠ 1} = 7 := by
    have e1 : Nat.card {x : ↥(quasithinGenFitting M) // (x : G) ≠ 1} =
        Nat.card {x : ↥(quasithinGenFitting M) // x ≠ 1} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun x =>
        ⟨fun h hx => h (congrArg Subtype.val hx), fun h hx => h (Subtype.ext hx)⟩)
    have e2 : Nat.card ↥(quasithinGenFitting M) =
        Nat.card (Option {x : ↥(quasithinGenFitting M) // x ≠ 1}) :=
      Nat.card_congr (Equiv.optionSubtypeNe (1 : ↥(quasithinGenFitting M))).symm
    rw [e1]
    rw [Finite.card_option] at e2
    have h8 : Nat.card ↥(quasithinGenFitting M) = 8 := hM.card
    omega
  exact hne

theorem thG_one {M : Subgroup G} (θ : ↥M →* SL(3, ZMod 2)) : thG θ 1 = 1 := by
  rw [thG_of_mem θ M.one_mem]
  exact map_one θ

theorem card_Qsub [Finite G] {M T : Subgroup G} (hM : G23Two M) (hTM : T ≤ M)
    (hT2 : IsPGroup 2 T) (hTidx : ¬ 2 ∣ (T.subgroupOf M).index) (θ : ↥M →* SL(3, ZMod 2))
    (hθk : θ.ker = (quasithinGenFitting M).subgroupOf M) :
    Nat.card ↥((T.subgroupOf M).map θ) = 8 := by
  have hVM : quasithinGenFitting M ≤ M := quasithinGenFitting_le M
  have hVT : quasithinGenFitting M ≤ T := G23Two.fitting_le_T hM hTM hT2 hTidx
  have hT64 : Nat.card T = 64 := G23Two.card_sylow hM hTM hT2 hTidx
  have hT'card : Nat.card ↥(T.subgroupOf M) = 64 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTM).toEquiv, hT64]
  have hker_iff : ∀ m : ↥M, θ m = 1 → (m : G) ∈ quasithinGenFitting M := fun m hm => by
    have hmem : m ∈ θ.ker := MonoidHom.mem_ker.mpr hm
    rw [hθk, Subgroup.mem_subgroupOf] at hmem
    exact hmem
  have hVker : ∀ v (hv : v ∈ quasithinGenFitting M), θ ⟨v, hVM hv⟩ = 1 := fun v hv =>
    MonoidHom.mem_ker.mp (show (⟨v, hVM hv⟩ : ↥M) ∈ θ.ker by
      rw [hθk, Subgroup.mem_subgroupOf]; exact hv)
  have e : (θ.comp (T.subgroupOf M).subtype).ker ≃ ↥(quasithinGenFitting M) :=
    { toFun := fun x => ⟨(x.1.1 : G), hker_iff x.1.1 (MonoidHom.mem_ker.mp x.2)⟩
      invFun := fun v => ⟨⟨⟨v.1, hVM v.2⟩, Subgroup.mem_subgroupOf.mpr (hVT v.2)⟩,
        MonoidHom.mem_ker.mpr (hVker v.1 v.2)⟩
      left_inv := fun x => Subtype.ext (Subtype.ext (Subtype.ext rfl))
      right_inv := fun v => Subtype.ext rfl }
  have hker : Nat.card (θ.comp (T.subgroupOf M).subtype).ker = 8 := by
    rw [Nat.card_congr e, hM.card]
  have hmul := Subgroup.card_ker_mul_card_range (θ.comp (T.subgroupOf M).subtype)
  rw [hker, hT'card] at hmul
  have hrange : (θ.comp (T.subgroupOf M).subtype).range = (T.subgroupOf M).map θ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hrange]
  omega

theorem fibre_card_four [Finite G] {M T : Subgroup G} (hM : G23Two M) (hTM : T ≤ M)
    (hT2 : IsPGroup 2 T) (hTidx : ¬ 2 ∣ (T.subgroupOf M).index) (θ : ↥M →* SL(3, ZMod 2))
    (hθk : θ.ker = (quasithinGenFitting M).subgroupOf M) {t y : G} (htT : t ∈ T)
    (hy : y ∈ M) (hyy : y * y = 1) (hty : thG θ t = thG θ y) (hu1 : thG θ y ≠ 1) :
    Nat.card {g : G // (g ∈ T ∧ g * g = 1 ∧ g ≠ 1) ∧ thG θ g = thG θ t} = 4 := by
  classical
  have hVM : quasithinGenFitting M ≤ M := quasithinGenFitting_le M
  have hVT : quasithinGenFitting M ≤ T := G23Two.fitting_le_T hM hTM hT2 hTidx
  have htM : t ∈ M := hTM htT
  have hu1' : thG θ t ≠ 1 := by rw [hty]; exact hu1
  have htV : t ∉ quasithinGenFitting M := by
    intro h
    exact hu1' ((thG_eq_one_iff θ hθk htM).mpr h)
  have hts : t * t ∈ quasithinGenFitting M := by
    rw [← thG_eq_one_iff θ hθk (M.mul_mem htM htM), thG_mul θ htM htM, hty,
      ← thG_mul θ hy hy, hyy, thG_one θ]
  have hvV : t⁻¹ * y ∈ quasithinGenFitting M := by
    refine (thG_eq_one_iff θ hθk (M.mul_mem (M.inv_mem htM) hy)).mp ?_
    rw [thG_mul θ (M.inv_mem htM) hy, thG_inv θ htM, hty, inv_mul_cancel]
  have hmemT : ∀ v : ↥(quasithinGenFitting M), thG θ (t * (v : G)) = thG θ t := fun v => by
    rw [thG_mul θ htM (hVM v.2), (thG_eq_one_iff θ hθk (hVM v.2)).mpr v.2, mul_one]
  have hne : ∀ v : ↥(quasithinGenFitting M), t * (v : G) ≠ 1 := fun v h =>
    hu1' (by rw [← hmemT v, h, thG_one θ])
  have hmemV : ∀ g : G, (g ∈ T ∧ g * g = 1 ∧ g ≠ 1) → thG θ g = thG θ t →
      t⁻¹ * g ∈ quasithinGenFitting M := by
    intro g hg hgt
    refine (thG_eq_one_iff θ hθk (M.mul_mem (M.inv_mem htM) (hTM hg.1))).mp ?_
    rw [thG_mul θ (M.inv_mem htM) (hTM hg.1), thG_inv θ htM, hgt, inv_mul_cancel]
  have hv0 : (t * ((⟨t⁻¹ * y, hvV⟩ : ↥(quasithinGenFitting M)) : G)) *
      (t * ((⟨t⁻¹ * y, hvV⟩ : ↥(quasithinGenFitting M)) : G)) = 1 := by
    show (t * (t⁻¹ * y)) * (t * (t⁻¹ * y)) = 1
    rw [mul_inv_cancel_left]
    exact hyy
  have e : {v : ↥(quasithinGenFitting M) // (t * (v : G)) * (t * (v : G)) = 1} ≃
      {g : G // (g ∈ T ∧ g * g = 1 ∧ g ≠ 1) ∧ thG θ g = thG θ t} :=
    { toFun := fun v => ⟨t * (v.1 : G), ⟨⟨T.mul_mem htT (hVT v.1.2), v.2, hne v.1⟩, hmemT v.1⟩⟩
      invFun := fun g => ⟨⟨t⁻¹ * g.1, hmemV g.1 g.2.1 g.2.2⟩, by
        show (t * (t⁻¹ * g.1)) * (t * (t⁻¹ * g.1)) = 1
        rw [mul_inv_cancel_left]
        exact g.2.1.2.1⟩
      left_inv := fun v => Subtype.ext (Subtype.ext (inv_mul_cancel_left t (v.1 : G)))
      right_inv := fun g => Subtype.ext (mul_inv_cancel_left t g.1) }
  have hcoset := card_coset_involutions (quasithinGenFitting M) (fun x hx y hy => G23Two.comm_fitting hM hx hy)
    (fun x hx => G23Two.sq_fitting hM hx) hM.card t (fun v hv => G23Two.conj_fitting htM hv) hts
    (G23Two.exists_conj_ne htM htV) _ hv0
  exact (Nat.card_congr e.symm).trans hcoset

open Classical in
theorem fibre_card_eq [Finite G] {M T : Subgroup G} (hM : G23Two M) (hTM : T ≤ M)
    (hT2 : IsPGroup 2 T) (hTidx : ¬ 2 ∣ (T.subgroupOf M).index) (θ : ↥M →* SL(3, ZMod 2))
    (hθk : θ.ker = (quasithinGenFitting M).subgroupOf M)
    (hgood : ∀ u : SL(3, ZMod 2), u * u = 1 → u ≠ 1 → ∃ y ∈ M, y * y = 1 ∧ thG θ y = u)
    (u : SL(3, ZMod 2)) :
    Nat.card {g : G // (g ∈ T ∧ g * g = 1 ∧ g ≠ 1) ∧ thG θ g = u} =
      (if u = 1 then 7 else 0) +
        (if u ∈ (T.subgroupOf M).map θ ∧ u * u = 1 ∧ u ≠ 1 then 4 else 0) := by
  by_cases hu1 : u = 1
  · subst hu1
    have h0 : ¬ ((1 : SL(3, ZMod 2)) ∈ (T.subgroupOf M).map θ ∧
        (1 : SL(3, ZMod 2)) * 1 = 1 ∧ (1 : SL(3, ZMod 2)) ≠ 1) := fun h => h.2.2 rfl
    rw [if_pos rfl, if_neg h0, add_zero]
    exact card_fibre_one hM hTM hT2 hTidx θ hθk
  · rw [if_neg hu1, zero_add]
    by_cases hQ : u ∈ (T.subgroupOf M).map θ ∧ u * u = 1
    · rw [if_pos ⟨hQ.1, hQ.2, hu1⟩]
      obtain ⟨m, hmT', hm⟩ := Subgroup.mem_map.mp hQ.1
      have htT : (m : G) ∈ T := Subgroup.mem_subgroupOf.mp hmT'
      have htu : thG θ (m : G) = u := by
        rw [thG_of_mem θ m.2]
        exact hm
      obtain ⟨y, hyM, hyy, hyu⟩ := hgood u hQ.2 hu1
      rw [← htu]
      exact fibre_card_four hM hTM hT2 hTidx θ hθk htT hyM hyy (by rw [htu, hyu])
        (by rw [hyu]; exact hu1)
    · rw [if_neg (fun h => hQ ⟨h.1, h.2.1⟩)]
      have hempty : IsEmpty {g : G // (g ∈ T ∧ g * g = 1 ∧ g ≠ 1) ∧ thG θ g = u} := by
        refine ⟨?_⟩
        rintro ⟨g, ⟨⟨hgT, hgg, _⟩, hgu⟩⟩
        apply hQ
        constructor
        · exact Subgroup.mem_map.mpr ⟨⟨g, hTM hgT⟩, Subgroup.mem_subgroupOf.mpr hgT,
            (thG_of_mem θ (hTM hgT)).symm.trans hgu⟩
        · rw [← hgu, ← thG_mul θ (hTM hgT) (hTM hgT), hgg, thG_one θ]
      exact Nat.card_of_isEmpty

open Classical in
theorem G23Two.card_involutions_sylow_of_outside [Finite G] {M T : Subgroup G} (hM : G23Two M)
    (hTM : T ≤ M) (hT2 : IsPGroup 2 T) (hTidx : ¬ 2 ∣ (T.subgroupOf M).index)
    (hR : ∃ x ∈ M, x * x = 1 ∧ x ∉ quasithinGenFitting M)
    (hconj : ∀ a b : SL(3, ZMod 2), a * a = 1 → a ≠ 1 → b * b = 1 → b ≠ 1 →
      ∃ g : SL(3, ZMod 2), g * a * g⁻¹ = b)
    (hsyl : ∀ P : Subgroup (SL(3, ZMod 2)), Nat.card P = 8 →
      Nat.card {u : SL(3, ZMod 2) // u ∈ P ∧ u * u = 1 ∧ u ≠ 1} = 5) :
    Nat.card {t : ↥T // orderOf t = 2} = 27 := by
  obtain ⟨θ, hθs, hθk⟩ := hM.quot
  obtain ⟨x, hxM, hxx, hxV⟩ := hR
  have hxθ : thG θ x ≠ 1 := fun h => hxV ((thG_eq_one_iff θ hθk hxM).mp h)
  have hxx' : thG θ x * thG θ x = 1 := by
    rw [← thG_mul θ hxM hxM, hxx, thG_one θ]
  have hgood : ∀ u : SL(3, ZMod 2), u * u = 1 → u ≠ 1 → ∃ y ∈ M, y * y = 1 ∧ thG θ y = u := by
    intro u hu hu1
    obtain ⟨g, hg⟩ := hconj (thG θ x) u hxx' hxθ hu hu1
    obtain ⟨m, hmM, hmg⟩ := thG_surj θ hθs g
    refine ⟨m * x * m⁻¹, M.mul_mem (M.mul_mem hmM hxM) (M.inv_mem hmM), ?_, ?_⟩
    · have e : m * x * m⁻¹ * (m * x * m⁻¹) = m * (x * x) * m⁻¹ := by group
      rw [e, hxx, mul_one, mul_inv_cancel]
    · rw [thG_mul θ (M.mul_mem hmM hxM) (M.inv_mem hmM), thG_mul θ hmM hxM, thG_inv θ hmM, hmg]
      exact hg
  have h1 : Nat.card {g : G // g ∈ T ∧ g * g = 1 ∧ g ≠ 1} =
      ∑ u : SL(3, ZMod 2), Nat.card {g : G // (g ∈ T ∧ g * g = 1 ∧ g ≠ 1) ∧ thG θ g = u} :=
    card_subtype_eq_sum_fibres _ _
  rw [card_involution_subtype_eq T, h1]
  simp only [fibre_card_eq hM hTM hT2 hTidx θ hθk hgood]
  rw [Finset.sum_add_distrib]
  have hcardQ := card_Qsub hM hTM hT2 hTidx θ hθk
  have hS := hsyl _ hcardQ
  have hcardF : (Finset.univ.filter (fun u : SL(3, ZMod 2) =>
      u ∈ (T.subgroupOf M).map θ ∧ u * u = 1 ∧ u ≠ 1)).card = 5 := by
    rw [← hS, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hsum2 : ∑ u : SL(3, ZMod 2),
      (if u ∈ (T.subgroupOf M).map θ ∧ u * u = 1 ∧ u ≠ 1 then 4 else 0) = 20 := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, hcardF]
  have hsum1 : ∑ u : SL(3, ZMod 2), (if u = 1 then 7 else 0) = 7 := by
    simp
  rw [hsum1, hsum2]

end CFSG.GH74.QTGen4.Recog.G23
