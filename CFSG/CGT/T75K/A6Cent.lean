module

public import CFSG.CGT.T75K.ExoticData
public import CFSG.CGT.T75K.A6Comm

public section

namespace CFSG.CGT.T75K

open CFSG.Open CFSG.CGT.Timmesfeld75 Module
open scoped MatrixGroups

section F2

variable {F : Type*} [Field F]

theorem one_add_one_of_two (hF2 : ∀ a : F, a = 0 ∨ a = 1) : (1 : F) + 1 = 0 := by
  rcases hF2 (1 + 1) with h | h
  · exact h
  · exfalso
    have h' : (1 : F) = 0 := by
      calc (1 : F) = 1 + 1 - 1 := by ring
        _ = 1 - 1 := by rw [h]
        _ = 0 := sub_self 1
    exact one_ne_zero h'

theorem add_self_of_two (hF2 : ∀ a : F, a = 0 ∨ a = 1) (a : F) : a + a = 0 := by
  rcases hF2 a with rfl | rfl
  · exact add_zero 0
  · exact one_add_one_of_two hF2

theorem eq_zero_or_one_of_card_two (hF : Nat.card F = 2) (a : F) : a = 0 ∨ a = 1 := by
  obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (0 : F)).1 hF
  by_cases ha : a = 0
  · exact Or.inl ha
  · right
    have h1 : a = y := huniq a ha
    have h2 : (1 : F) = y := huniq 1 one_ne_zero
    rw [h1, h2]

end F2

namespace LinData

variable {G : Type} [Group G] {T H : Subgroup G} {n m : ℕ}

theorem mem_T_of_centralizes (D : LinData T H n m) {z : G} (hz : z ∈ H) (hc : ∀ t ∈ T, z * t * z⁻¹ = t) : z ∈ T := by
  rw [← mat_eq_one_iff (D := D) hz]
  apply sv_ext
  intro y
  obtain ⟨t, ht, rfl⟩ := exists_vec (D := D) y
  obtain ⟨-, hv⟩ := vec_conj (D := D) hz ht
  rw [hc t ht] at hv
  rw [sv_one]
  exact hv.symm

end LinData

section Lift

variable {G : Type} [Group G] {T H : Subgroup G} {n m : ℕ}

theorem exists_lift_transv (D : LinData T H n m) {fh : Dual (GaloisField 2 m) (Fin n → GaloisField 2 m)}
    {p : Fin n → GaloisField 2 m} (hfp : fh p = 0) :
    ∃ h ∈ H, ∀ y, sv (D.mat h) y = y + fh y • p := by
  obtain ⟨τ, hτ, -⟩ := exists_transv hfp
  obtain ⟨h, hH, hm⟩ := LinData.exists_mat (D := D) τ
  exact ⟨h, hH, fun y => by rw [hm]; exact hτ y⟩

theorem lift_comm_T (D : LinData T H n m) (hF2 : ∀ a : GaloisField 2 m, a = 0 ∨ a = 1)
    (hHnorm : ∀ f ∈ Subgroup.normalizer (T : Set G), ∀ h ∈ H, f * h * f⁻¹ ∈ H)
    {u : G} (hu : u ∈ Subgroup.normalizer (T : Set G))
    {fh : Dual (GaloisField 2 m) (Fin n → GaloisField 2 m)}
    (hP : ∀ t ∈ T, fh (D.vec (cm t u)) = 0)
    {b : G} (hbT : b ∈ T) (hbu : b * u = u * b)
    {h : G} (hh : h ∈ H) (hact : ∀ y, sv (D.mat h) y = y + fh y • D.vec b) :
    h * u * h⁻¹ * u⁻¹ ∈ T := by
  have hcj : ∀ x ∈ T, h * x * h⁻¹ ∈ T ∧
      D.vec (h * x * h⁻¹) = D.vec x + fh (D.vec x) • D.vec b := by
    intro x hx
    obtain ⟨hm, hv⟩ := LinData.vec_conj (D := D) hh hx
    exact ⟨hm, by rw [hv, hact]⟩
  have hform0 : ∀ x ∈ T, fh (D.vec x) = 0 → h * x * h⁻¹ = x := by
    intro x hx h0
    obtain ⟨hm, hv⟩ := hcj x hx
    apply LinData.vec_inj (D := D) hm hx
    rw [hv, h0, zero_smul, add_zero]
  have hform1 : ∀ x ∈ T, fh (D.vec x) ≠ 0 → h * x * h⁻¹ = x * b := by
    intro x hx h1
    obtain ⟨hm, hv⟩ := hcj x hx
    have h1' : fh (D.vec x) = 1 := (hF2 _).resolve_left h1
    apply LinData.vec_inj (D := D) hm (T.mul_mem hx hbT)
    rw [hv, h1', one_smul, LinData.vec_mul hx hbT]
  have hconjstab : ∀ t ∈ T, u * t * u⁻¹ ∈ T ∧ fh (D.vec (u * t * u⁻¹)) = fh (D.vec t) := by
    intro t ht
    have hx : u * t * u⁻¹ ∈ T := conj_mem_of_mem_normalizer hu ht
    refine ⟨hx, ?_⟩
    have hcmT : cm t u ∈ T := cm_mem_T ht hu
    have e : u * t * u⁻¹ = (cm t u)⁻¹ * t := by unfold cm; group
    rw [e, LinData.vec_mul (T.inv_mem hcmT) ht, LinData.vec_inv hcmT, map_add, map_neg, hP t ht,
      neg_zero, zero_add]
  have hcomm : ∀ t ∈ T, h * (u * t * u⁻¹) * h⁻¹ = u * (h * t * h⁻¹) * u⁻¹ := by
    intro t ht
    obtain ⟨hx, hfx⟩ := hconjstab t ht
    by_cases h0 : fh (D.vec t) = 0
    · have h0' : fh (D.vec (u * t * u⁻¹)) = 0 := by rw [hfx, h0]
      rw [hform0 _ hx h0', hform0 _ ht h0]
    · have h1' : fh (D.vec (u * t * u⁻¹)) ≠ 0 := by rw [hfx]; exact h0
      rw [hform1 _ hx h1', hform1 _ ht h0]
      have hub : u * b * u⁻¹ = b := by
        rw [mul_inv_eq_iff_eq_mul]
        exact hbu.symm
      calc u * t * u⁻¹ * b = u * t * u⁻¹ * (u * b * u⁻¹) := by rw [hub]
        _ = u * (t * b) * u⁻¹ := by group
  have hzH : h * u * h⁻¹ * u⁻¹ ∈ H := by
    have h1 : u * h⁻¹ * u⁻¹ ∈ H := hHnorm u hu h⁻¹ (H.inv_mem hh)
    have e : h * u * h⁻¹ * u⁻¹ = h * (u * h⁻¹ * u⁻¹) := by group
    rw [e]
    exact H.mul_mem hh h1
  have hzc : ∀ t ∈ T, (h * u * h⁻¹ * u⁻¹) * t * (h * u * h⁻¹ * u⁻¹)⁻¹ = t := by
    intro t ht
    have hu' : u⁻¹ ∈ Subgroup.normalizer (T : Set G) := (Subgroup.normalizer _).inv_mem hu
    have hh' : h⁻¹ ∈ Subgroup.normalizer (T : Set G) :=
      (Subgroup.normalizer _).inv_mem (D.hHN hh)
    have ht' : u⁻¹ * t * u ∈ T := by simpa using conj_mem_of_mem_normalizer hu' ht
    have hs : h⁻¹ * (u⁻¹ * t * u) * h ∈ T := by simpa using conj_mem_of_mem_normalizer hh' ht'
    have key := hcomm _ hs
    have e1 : h * (h⁻¹ * (u⁻¹ * t * u) * h) * h⁻¹ = u⁻¹ * t * u := by group
    rw [e1] at key
    calc (h * u * h⁻¹ * u⁻¹) * t * (h * u * h⁻¹ * u⁻¹)⁻¹
        = h * (u * (h⁻¹ * (u⁻¹ * t * u) * h) * u⁻¹) * h⁻¹ := by group
      _ = u * (u⁻¹ * t * u) * u⁻¹ := key
      _ = t := by group
  exact LinData.mem_T_of_centralizes D hzH hzc

theorem comm_mem_cent (hT : IsElemAbelian 2 T) {u : G} (hu2 : u * u = 1) {h : G}
    (hs : h * u * h⁻¹ * u⁻¹ ∈ T) :
    h * u * h⁻¹ * u⁻¹ ∈ Subgroup.centralizer ({u} : Set G) := by
  have hss : (h * u * h⁻¹ * u⁻¹) * (h * u * h⁻¹ * u⁻¹) = 1 := elemAbelian_mul_self hT hs
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have h1 : ((h * u * h⁻¹ * u⁻¹) * u) * ((h * u * h⁻¹ * u⁻¹) * u) = 1 := by
    have e : (h * u * h⁻¹ * u⁻¹) * u = h * u * h⁻¹ := by group
    rw [e]
    calc h * u * h⁻¹ * (h * u * h⁻¹) = h * (u * u) * h⁻¹ := by group
      _ = 1 := by rw [hu2]; group
  have h3 : (h * u * h⁻¹ * u⁻¹) * u * (h * u * h⁻¹ * u⁻¹) = u := by
    have h4 : ((h * u * h⁻¹ * u⁻¹) * u * (h * u * h⁻¹ * u⁻¹)) * u = 1 := by
      calc ((h * u * h⁻¹ * u⁻¹) * u * (h * u * h⁻¹ * u⁻¹)) * u
          = ((h * u * h⁻¹ * u⁻¹) * u) * ((h * u * h⁻¹ * u⁻¹) * u) := by group
        _ = 1 := h1
    rw [eq_inv_of_mul_eq_one_left h4, hui]
  have hsi : (h * u * h⁻¹ * u⁻¹)⁻¹ = h * u * h⁻¹ * u⁻¹ := inv_eq_of_mul_eq_one_right hss
  have h5 := eq_mul_inv_of_mul_eq h3
  rw [hsi] at h5
  exact Subgroup.mem_centralizer_singleton_iff.2 h5

theorem act_prod (D : LinData T H n m) (hF2 : ∀ a : GaloisField 2 m, a = 0 ∨ a = 1)
    {fh : Dual (GaloisField 2 m) (Fin n → GaloisField 2 m)} {b b' : G}
    (hfb : fh (D.vec b) = 0) (hfb' : fh (D.vec b') = 0) {h h' : G} (hh : h ∈ H) (hh' : h' ∈ H)
    {t : G} (ht : t ∈ T) (hact : ∀ y, sv (D.mat h) y = y + fh y • D.vec b)
    (hact' : ∀ y, sv (D.mat h') y = y + fh y • D.vec b') :
    ∀ y, sv (D.mat (h'⁻¹ * t * h)) y = y + fh y • (D.vec b + D.vec b') := by
  have hH' : h'⁻¹ ∈ H := H.inv_mem hh'
  have htH : t ∈ H := D.hTH ht
  have hmat : D.mat (h'⁻¹ * t * h) = (D.mat h')⁻¹ * D.mat h := by
    rw [LinData.mat_mul (H.mul_mem hH' htH) hh, LinData.mat_mul hH' htH, LinData.mat_inv hh',
      LinData.mat_of_mem_T ht, mul_one]
  have hv' : sv (D.mat h') (D.vec b') = D.vec b' := by
    rw [hact' (D.vec b'), hfb', zero_smul, add_zero]
  have hinv : ∀ y, sv (D.mat h')⁻¹ y = y + fh y • D.vec b' := by
    intro y
    have h2 : sv (D.mat h') (sv (D.mat h') y) = y := by
      rw [hact' y, sv_add, sv_smul, hv', hact' y]
      calc y + fh y • D.vec b' + fh y • D.vec b' = y + (fh y + fh y) • D.vec b' := by module
        _ = y := by rw [add_self_of_two hF2, zero_smul, add_zero]
    calc sv (D.mat h')⁻¹ y = sv (D.mat h')⁻¹ (sv (D.mat h') (sv (D.mat h') y)) := by rw [h2]
      _ = sv (D.mat h') y := sv_sv_inv _ _
      _ = y + fh y • D.vec b' := hact' y
  have hv : sv (D.mat h')⁻¹ (D.vec b) = D.vec b := by
    rw [hinv, hfb, zero_smul, add_zero]
  intro y
  rw [hmat, sv_mul, hact y, sv_add, sv_smul, hinv y, hv]
  module

theorem exists_centralizing [Finite G] (D : LinData T H n m)
    (hFc : Nat.card (GaloisField 2 m) = 2) (hT : IsElemAbelian 2 T)
    (hHnorm : ∀ f ∈ Subgroup.normalizer (T : Set G), ∀ h ∈ H, f * h * f⁻¹ ∈ H)
    {u : G} (hu : u ∈ Subgroup.normalizer (T : Set G)) (hu2 : u * u = 1)
    (hcard : Nat.card T = 4 * Nat.card ↥(T ⊓ Subgroup.centralizer ({u} : Set G)))
    (h8 : 8 ≤ Nat.card ↥(T ⊓ Subgroup.centralizer ({u} : Set G))) :
    ∃ (Lm : G → Prop) (p a₀ g : G),
      p ∈ T ⊓ Subgroup.centralizer ({u} : Set G) ∧ p ≠ 1 ∧ Lm p ∧
      a₀ ∈ T ⊓ Subgroup.centralizer ({u} : Set G) ∧ ¬ Lm a₀ ∧ g ∈ H ∧ g * u * g⁻¹ = u ∧
      (∀ t ∈ T, Lm t → g * t * g⁻¹ = t) ∧ (∀ t ∈ T, ¬ Lm t → g * t * g⁻¹ = t * p) := by
  classical
  have hF2 : ∀ a : GaloisField 2 m, a = 0 ∨ a = 1 := eq_zero_or_one_of_card_two hFc
  have hF11 : (1 : GaloisField 2 m) + 1 = 0 := one_add_one_of_two hF2
  set A : Subgroup G := T ⊓ Subgroup.centralizer ({u} : Set G) with hA
  have hAT : A ≤ T := inf_le_left
  have hAu : ∀ a ∈ A, a * u = u * a := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.1 ha.2
  have hApos : 0 < Nat.card A := Nat.card_pos
  let θ : ↥T →* ↥A := thetaHom hT hu hu2
  let P : Subgroup ↥A := θ.range
  have hPcard : Nat.card P = 4 := by
    have h : Nat.card A * Nat.card θ.range = Nat.card T := card_range_thetaHom hT hu hu2
    have h' : Nat.card A * Nat.card P = Nat.card A * 4 := by
      show Nat.card A * Nat.card θ.range = _
      rw [h, hcard]
      ring
    exact Nat.eq_of_mul_eq_mul_left hApos h'
  have hPmem : ∀ q : ↥A, q ∈ P → ∃ t ∈ T, (q : G) = cm t u := by
    intro q hq
    obtain ⟨t, rfl⟩ := MonoidHom.mem_range.1 hq
    exact ⟨t, t.2, rfl⟩
  let W : Submodule (GaloisField 2 m) (Fin n → GaloisField 2 m) :=
    { carrier := {w | ∃ q ∈ P, D.vec ((q : ↥A) : G) = w}
      add_mem' := by
        rintro _ _ ⟨q₁, hq₁, rfl⟩ ⟨q₂, hq₂, rfl⟩
        exact ⟨q₁ * q₂, P.mul_mem hq₁ hq₂, LinData.vec_mul (D := D) (hAT q₁.2) (hAT q₂.2)⟩
      zero_mem' := ⟨1, P.one_mem, LinData.vec_one (D := D)⟩
      smul_mem' := by
        rintro a _ ⟨q, hq, rfl⟩
        rcases hF2 a with rfl | rfl
        · exact ⟨1, P.one_mem, by rw [zero_smul]; exact LinData.vec_one (D := D)⟩
        · exact ⟨q, hq, by rw [one_smul]⟩ }
  obtain ⟨q₀, hq₀⟩ : ∃ q₀ : ↥A, q₀ ∉ P := by
    by_contra hcon
    push Not at hcon
    have hPtop : P = ⊤ := (Subgroup.eq_top_iff' _).2 hcon
    rw [hPtop, Subgroup.card_top] at hPcard
    omega
  have hvq₀ : D.vec ((q₀ : ↥A) : G) ∉ W := by
    rintro ⟨q, hq, hqq⟩
    apply hq₀
    have h1 : ((q : ↥A) : G) = ((q₀ : ↥A) : G) :=
      LinData.vec_inj (D := D) (hAT q.2) (hAT q₀.2) hqq
    have hqq₀ : q = q₀ := Subtype.ext h1
    rw [← hqq₀]
    exact hq
  obtain ⟨fh, hfv, hfW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hvq₀ inferInstance
  have hfW' : ∀ w ∈ W, fh w = 0 := by
    intro w hw
    have h1 : fh w ∈ W.map fh := Submodule.mem_map_of_mem hw
    rw [hfW] at h1
    exact (Submodule.mem_bot _).1 h1
  have hP0 : ∀ t ∈ T, fh (D.vec (cm t u)) = 0 := fun t ht =>
    hfW' _ ⟨θ ⟨t, ht⟩, MonoidHom.mem_range.2 ⟨⟨t, ht⟩, rfl⟩, rfl⟩
  have hfq₀ : fh (D.vec ((q₀ : ↥A) : G)) = 1 := (hF2 _).resolve_left hfv
  let χ : ↥A →* Multiplicative (GaloisField 2 m) :=
    { toFun := fun a => Multiplicative.ofAdd (fh (D.vec (a : G)))
      map_one' := by
        show Multiplicative.ofAdd (fh (D.vec ((1 : ↥A) : G))) = 1
        rw [show ((1 : ↥A) : G) = 1 from rfl, LinData.vec_one (D := D), map_zero]
        rfl
      map_mul' := fun a b => by
        show Multiplicative.ofAdd (fh (D.vec (((a * b : ↥A)) : G))) = _
        rw [show (((a * b : ↥A)) : G) = (a : G) * (b : G) from rfl,
          LinData.vec_mul (D := D) (hAT a.2) (hAT b.2), map_add]
        rfl }
  let K : Subgroup ↥A := χ.ker
  have hKmem : ∀ b : ↥K, fh (D.vec (((b : ↥A)) : G)) = 0 := by
    intro b
    have h1 : χ (b : ↥A) = 1 := b.2
    exact ofAdd_eq_one.1 h1
  have hKcard : Nat.card A ≤ 2 * Nat.card K := by
    have h1 : Nat.card χ.ker * Nat.card χ.range = Nat.card ↥A :=
      Subgroup.card_ker_mul_card_range χ
    have h2 : Nat.card χ.range ≤ 2 := by
      calc Nat.card χ.range ≤ Nat.card (Multiplicative (GaloisField 2 m)) :=
            Subgroup.card_le_card_group _
        _ = 2 := by
          rw [Nat.card_congr (Multiplicative.ofAdd : GaloisField 2 m ≃
            Multiplicative (GaloisField 2 m)).symm]
          exact hFc
    calc Nat.card A = Nat.card χ.ker * Nat.card χ.range := h1.symm
      _ ≤ Nat.card K * 2 := Nat.mul_le_mul_left _ h2
      _ = 2 * Nat.card K := by ring
  have hlift : ∀ b : ↥K, ∃ h ∈ H, ∀ y, sv (D.mat h) y = y + fh y • D.vec (((b : ↥A)) : G) :=
    fun b => exists_lift_transv D (hKmem b)
  choose hh hhH hhact using hlift
  have hbT : ∀ b : ↥K, ((b : ↥A) : G) ∈ T := fun b => hAT b.1.2
  have hbu : ∀ b : ↥K, ((b : ↥A) : G) * u = u * ((b : ↥A) : G) := fun b => hAu _ b.1.2
  have hsT : ∀ b : ↥K, hh b * u * (hh b)⁻¹ * u⁻¹ ∈ T := fun b =>
    lift_comm_T D hF2 hHnorm hu hP0 (hbT b) (hbu b) (hhH b) (hhact b)
  have hsA : ∀ b : ↥K, hh b * u * (hh b)⁻¹ * u⁻¹ ∈ A := fun b =>
    ⟨hsT b, comm_mem_cent hT hu2 (hsT b)⟩
  let κ : ↥K → ↥A ⧸ P := fun b => QuotientGroup.mk (⟨_, hsA b⟩ : ↥A)
  have hQcard : Nat.card A = Nat.card (↥A ⧸ P) * 4 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup P, hPcard]
  have hlt : Nat.card (↥A ⧸ P) < Nat.card K := by
    have hQpos : 0 < Nat.card (↥A ⧸ P) := Nat.card_pos
    omega
  have : Fintype ↥K := Fintype.ofFinite _
  have : Fintype (↥A ⧸ P) := Fintype.ofFinite _
  obtain ⟨b, b', hne, hκ⟩ := Fintype.exists_ne_map_eq_of_card_lt κ (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hlt)
  have hκ' : (⟨_, hsA b⟩ : ↥A)⁻¹ * ⟨_, hsA b'⟩ ∈ P := QuotientGroup.eq.1 hκ
  obtain ⟨t, htT, htcm⟩ := hPmem _ hκ'
  have hrel : (hh b * u * (hh b)⁻¹ * u⁻¹)⁻¹ * (hh b' * u * (hh b')⁻¹ * u⁻¹) = cm t u := htcm
  have hy : hh b' * u * (hh b')⁻¹ = t * (hh b * u * (hh b)⁻¹) * t⁻¹ := by
    have hcomm : t * (hh b * u * (hh b)⁻¹ * u⁻¹) = (hh b * u * (hh b)⁻¹ * u⁻¹) * t :=
      elemAbelian_mul_comm hT htT (hsT b)
    have e3 : hh b' * u * (hh b')⁻¹ * u⁻¹ = (hh b * u * (hh b)⁻¹ * u⁻¹) * cm t u := by
      rw [← hrel]
      group
    calc hh b' * u * (hh b')⁻¹ = (hh b' * u * (hh b')⁻¹ * u⁻¹) * u := by group
      _ = (hh b * u * (hh b)⁻¹ * u⁻¹) * cm t u * u := by rw [e3]
      _ = (hh b * u * (hh b)⁻¹ * u⁻¹) * (t * u * t⁻¹) := by unfold cm; group
      _ = (t * (hh b * u * (hh b)⁻¹ * u⁻¹) * t⁻¹) * (t * u * t⁻¹) := by rw [hcomm]; group
      _ = t * (hh b * u * (hh b)⁻¹) * t⁻¹ := by group
  have hgH : (hh b')⁻¹ * t * hh b ∈ H :=
    H.mul_mem (H.mul_mem (H.inv_mem (hhH b')) (D.hTH htT)) (hhH b)
  have hgu : ((hh b')⁻¹ * t * hh b) * u * ((hh b')⁻¹ * t * hh b)⁻¹ = u := by
    calc ((hh b')⁻¹ * t * hh b) * u * ((hh b')⁻¹ * t * hh b)⁻¹
        = (hh b')⁻¹ * (t * (hh b * u * (hh b)⁻¹) * t⁻¹) * hh b' := by group
      _ = (hh b')⁻¹ * (hh b' * u * (hh b')⁻¹) * hh b' := by rw [← hy]
      _ = u := by group
  have hactg : ∀ y, sv (D.mat ((hh b')⁻¹ * t * hh b)) y =
      y + fh y • (D.vec (((b : ↥A)) : G) + D.vec (((b' : ↥A)) : G)) :=
    act_prod D hF2 (hKmem b) (hKmem b') (hhH b) (hhH b') htT (hhact b) (hhact b')
  have hpT : ((b : ↥A) : G) * ((b' : ↥A) : G) ∈ T := T.mul_mem (hbT b) (hbT b')
  refine ⟨fun x => fh (D.vec x) = 0, ((b : ↥A) : G) * ((b' : ↥A) : G), (q₀ : G),
    (hh b')⁻¹ * t * hh b, A.mul_mem b.1.2 b'.1.2, ?_, ?_, q₀.2, ?_, hgH, hgu, ?_, ?_⟩
  · intro h1
    apply hne
    have hbb : ((b : ↥A) : G) = ((b' : ↥A) : G) := by
      have hb' : ((b' : ↥A) : G) = ((b : ↥A) : G)⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [hb', elemAbelian_inv hT (hbT b)]
    exact Subtype.ext (Subtype.ext hbb)
  · show fh (D.vec (((b : ↥A) : G) * ((b' : ↥A) : G))) = 0
    rw [LinData.vec_mul (D := D) (hbT b) (hbT b'), map_add, hKmem b, hKmem b', add_zero]
  · show ¬ fh (D.vec ((q₀ : ↥A) : G)) = 0
    rw [hfq₀]
    exact one_ne_zero
  · intro x hx h0
    have h0' : fh (D.vec x) = 0 := h0
    obtain ⟨hm, hv⟩ := LinData.vec_conj (D := D) hgH hx
    apply LinData.vec_inj (D := D) hm hx
    rw [hv, hactg, h0', zero_smul, add_zero]
  · intro x hx h0
    have h1 : fh (D.vec x) = 1 := (hF2 _).resolve_left h0
    obtain ⟨hm, hv⟩ := LinData.vec_conj (D := D) hgH hx
    apply LinData.vec_inj (D := D) hm (T.mul_mem hx hpT)
    rw [hv, hactg, h1, one_smul, LinData.vec_mul (D := D) hx hpT,
      LinData.vec_mul (D := D) (hbT b) (hbT b')]

end Lift

end CFSG.CGT.T75K
