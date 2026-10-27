module

public import CFSG.CGT.PushingUpLit.T2KSW.RD
public import CFSG.CGT.PushingUpLit.T2KSW.Coord
public import CFSG.CGT.PushingUpLit.T2KR.Asc78Gen

public section

namespace CFSG.CGT.PushingUpLit.T2KSW

open CFSG CFSG.ABGLocalTools CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.T2K
open scoped commutatorElement

namespace WeakCl

variable {G : Type} [Group G] [Finite G]

theorem card_lt_of_lt_aux {H K : Subgroup G} (h : H < K) : Nat.card H < Nat.card K := by
  have h1 := Subgroup.card_le_of_le h.le
  refine lt_of_le_of_ne h1 fun heq => h.ne ?_
  exact Subgroup.eq_of_le_of_card_ge h.le heq.ge

theorem lt_inf_normalizer_aux {X S : Subgroup G} (hS : IsPGroup 2 S) (hXS : X < S) :
    X < S ⊓ Subgroup.normalizer (X : Set G) := by
  have : Group.IsNilpotent S := hS.isNilpotent
  have hlt : X.subgroupOf S < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    exact hXS.ne (le_antisymm hXS.le (Subgroup.subgroupOf_eq_top.1 h))
  obtain ⟨x, hxN, hxQ⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  rw [← Subgroup.subgroupOf_normalizer_eq hXS.le] at hxN
  refine lt_of_le_of_ne (le_inf hXS.le Subgroup.le_normalizer) fun h => hxQ ?_
  have hx : (x : G) ∈ S ⊓ Subgroup.normalizer (X : Set G) := Subgroup.mem_inf.2 ⟨x.2, hxN⟩
  rw [← h] at hx
  exact hx

theorem mem_of_map_conj_le_aux {M T : Subgroup G} (hT : IsSylowOf 2 T M)
    (hNT : Subgroup.normalizer (T : Set G) ≤ M) {k : G}
    (hk : T.map (MulAut.conj k).toMonoidHom ≤ M) : k ∈ M := by
  have hP : IsPGroup 2 ↥(T.map (MulAut.conj k).toMonoidHom) := hT.isPGroup.map _
  obtain ⟨m, hm, hmT⟩ := exists_conj_le_of_isPGroup hT hP hk
  have e : (T.map (MulAut.conj k).toMonoidHom).map (MulAut.conj m).toMonoidHom =
      T.map (MulAut.conj (m * k)).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [e] at hmT
  have hmk : m * k ∈ Subgroup.normalizer (T : Set G) :=
    mem_normalizer_of_map_conj_eq (Subgroup.eq_of_le_of_card_ge hmT (by rw [card_map_conj]))
  have := M.mul_mem (M.inv_mem hm) (hNT hmk)
  simpa using this

theorem exists_larger {M T T₁ : Subgroup G} (hT : IsSylowOf 2 T M)
    (hNT : Subgroup.normalizer (T : Set G) ≤ M) (hT₁T : T₁ ≤ T)
    (hnorm : ∀ X : Subgroup G, T₁ ≤ X → X ≤ T → T ≤ Subgroup.normalizer (X : Set G))
    (hNX : ∀ X : Subgroup G, T₁ ≤ X → X ≤ T → Subgroup.normalizer (X : Set G) ≤ M)
    {y : G} (hy : T₁ ≤ M.map (MulAut.conj y).toMonoidHom) (hyM : y ∉ M) :
    ∃ y' : G, y' ∉ M ∧ T₁ ≤ M.map (MulAut.conj y').toMonoidHom ∧
      Nat.card ↥(T ⊓ M.map (MulAut.conj y).toMonoidHom) <
        Nat.card ↥(T ⊓ M.map (MulAut.conj y').toMonoidHom) := by
  set X : Subgroup G := T ⊓ M.map (MulAut.conj y).toMonoidHom with hX
  have hXT : X ≤ T := inf_le_left
  have hT₁X : T₁ ≤ X := le_inf hT₁T hy
  have hX2 : IsPGroup 2 X := hT.isPGroup.to_le hXT
  have hTM : T ≤ M := hT.le
  have hXne : X ≠ T := by
    intro h
    have hTy : T ≤ M.map (MulAut.conj y).toMonoidHom := fun t ht => by
      have : t ∈ X := h ▸ ht
      exact this.2
    have : T.map (MulAut.conj y⁻¹).toMonoidHom ≤ M := by
      rintro _ ⟨t, ht, rfl⟩
      have h1 := (mem_map_conj_iff y M t).1 (hTy ht)
      simpa [MulAut.conj_apply] using h1
    have h2 := mem_of_map_conj_le_aux hT hNT this
    exact hyM (by simpa using M.inv_mem h2)
  have hXcard : Nat.card X < Nat.card T := card_lt_of_lt_aux (lt_of_le_of_ne hXT hXne)
  have hXy : X.map (MulAut.conj y⁻¹).toMonoidHom ≤ M := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 := (mem_map_conj_iff y M x).1 hx.2
    simpa [MulAut.conj_apply] using h1
  obtain ⟨k, hkM, hkT⟩ := exists_conj_le_of_isPGroup hT (hX2.map _) hXy
  set y₁ : G := y * k⁻¹ with hy₁
  set S : Subgroup G := T.map (MulAut.conj y₁).toMonoidHom with hS
  have hS2 : IsPGroup 2 S := hT.isPGroup.map _
  have hSc : Nat.card S = Nat.card T := card_map_conj T y₁
  have hXS : X ≤ S := by
    intro x hx
    rw [hS, mem_map_conj_iff]
    have h1 : k * (y⁻¹ * x * y) * k⁻¹ ∈ T := by
      apply hkT
      exact ⟨y⁻¹ * x * y, ⟨x, hx, by simp⟩, by simp [MulAut.conj_apply]⟩
    have e : y₁⁻¹ * x * y₁ = k * (y⁻¹ * x * y) * k⁻¹ := by simp [hy₁, mul_assoc]
    rw [e]
    exact h1
  have hXSlt : X < S := lt_of_le_of_ne hXS fun h => by
    have : Nat.card X = Nat.card T := by rw [← hSc, ← h]
    omega
  set P : Subgroup G := S ⊓ Subgroup.normalizer (X : Set G) with hP
  have hXP : X < P := lt_inf_normalizer_aux hS2 hXSlt
  have hPM : P ≤ M := fun p hp => hNX X hT₁X hXT hp.2
  have hP2 : IsPGroup 2 P := hS2.to_le inf_le_left
  have hTN : T ≤ M ⊓ Subgroup.normalizer (X : Set G) :=
    le_inf hTM (hnorm X hT₁X hXT)
  have hT' : IsSylowOf 2 T (M ⊓ Subgroup.normalizer (X : Set G)) := hT.of_le hTN inf_le_left
  obtain ⟨m, hmMN, hmP⟩ :=
    exists_conj_le_of_isPGroup hT' hP2 (le_inf hPM inf_le_right)
  refine ⟨m * y₁, ?_, ?_, ?_⟩
  · intro h
    have h1 : y ∈ M := by
      have : m * (y * k⁻¹) ∈ M := h
      have h2 := M.mul_mem (M.mul_mem (M.inv_mem hmMN.1) this) hkM
      simpa [mul_assoc] using h2
    exact hyM h1
  · intro t ht
    rw [mem_map_conj_iff]
    have hn : m ∈ Subgroup.normalizer (X : Set G) := hmMN.2
    have hx : m⁻¹ * t * m ∈ X := by
      have h1 := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hn) t).1 (hT₁X ht)
      simpa [mul_assoc] using h1
    have hxS : m⁻¹ * t * m ∈ S := (inf_le_left : P ≤ S) (hXP.le hx)
    have h1 := (mem_map_conj_iff y₁ T _).1 hxS
    have e : (m * y₁)⁻¹ * t * (m * y₁) = y₁⁻¹ * (m⁻¹ * t * m) * y₁ := by group
    rw [e]
    exact hTM h1
  · have hPm : Nat.card (P.map (MulAut.conj m).toMonoidHom) = Nat.card P := card_map_conj P m
    have hsub : P.map (MulAut.conj m).toMonoidHom ≤
        T ⊓ M.map (MulAut.conj (m * y₁)).toMonoidHom := by
      refine le_inf hmP fun q hq => ?_
      obtain ⟨p, hp, rfl⟩ := hq
      rw [mem_map_conj_iff]
      have h1 := (mem_map_conj_iff y₁ T p).1 (hp.1 : p ∈ S)
      have e : (m * y₁)⁻¹ * (MulAut.conj m).toMonoidHom p * (m * y₁) = y₁⁻¹ * p * y₁ := by
        simp [MulAut.conj_apply, mul_assoc]
      rw [e]
      exact hTM h1
    have h2 := Subgroup.card_le_of_le hsub
    have h3 := card_lt_of_lt_aux hXP
    omega

theorem mem_of_le_map_conj {M T T₁ : Subgroup G} (hT : IsSylowOf 2 T M)
    (hNT : Subgroup.normalizer (T : Set G) ≤ M) (hT₁T : T₁ ≤ T)
    (hnorm : ∀ X : Subgroup G, T₁ ≤ X → X ≤ T → T ≤ Subgroup.normalizer (X : Set G))
    (hNX : ∀ X : Subgroup G, T₁ ≤ X → X ≤ T → Subgroup.normalizer (X : Set G) ≤ M)
    {y : G} (hy : T₁ ≤ M.map (MulAut.conj y).toMonoidHom) : y ∈ M := by
  suffices H : ∀ d : ℕ, ∀ y : G, T₁ ≤ M.map (MulAut.conj y).toMonoidHom →
      Nat.card T - Nat.card ↥(T ⊓ M.map (MulAut.conj y).toMonoidHom) = d → y ∈ M from
    H _ y hy rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro y hy hd
    by_contra hyM
    obtain ⟨y', hy'M, hy', hlt⟩ := exists_larger hT hNT hT₁T hnorm hNX hy hyM
    have hle : Nat.card ↥(T ⊓ M.map (MulAut.conj y').toMonoidHom) ≤ Nat.card T :=
      Subgroup.card_le_of_le inf_le_left
    exact hy'M (ih _ (by omega) y' hy' rfl)


section Chi

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Campbell
  CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.T2KR

variable {L M : Subgroup G} {n : ℕ} (H : CoordData G L M n)

@[expose] noncomputable def vecC (w : Fin 2 → Fq n) : G := Classical.choose (H.D.exists_ψe w)

theorem vecC_mem (w : Fin 2 → Fq n) : vecC H w ∈ blockU L :=
  (Classical.choose_spec (H.D.exists_ψe w)).1

theorem ψe_vecC (w : Fin 2 → Fq n) : H.D.ψe (vecC H w) = w :=
  (Classical.choose_spec (H.D.exists_ψe w)).2

@[expose] noncomputable def act (m : G) (w : Fin 2 → Fq n) : Fin 2 → Fq n :=
  H.D.ψe (m * vecC H w * m⁻¹)

include H in
theorem act_vec {m : G} (hm : m ∈ M) {v : G} (hv : v ∈ blockU L) :
    act H m (H.D.ψe v) = H.D.ψe (m * v * m⁻¹) := by
  have hmN : m ∈ Subgroup.normalizer (L : Set G) := H.normal hm
  set v₀ : G := vecC H (H.D.ψe v) with hv₀
  have hv₀V : v₀ ∈ blockU L := vecC_mem H _
  have hψ : H.D.ψe v₀ = H.D.ψe v := ψe_vecC H _
  have hz : v₀⁻¹ * v ∈ blockZ L := by
    refine (H.D.ψe_eq_zero_iff (mul_mem (inv_mem hv₀V) hv)).1 ?_
    rw [H.D.ψe_mul (inv_mem hv₀V) hv, H.D.ψe_inv hv₀V, hψ]
    abel
  have hzc : m * (v₀⁻¹ * v) * m⁻¹ ∈ blockZ L := conj_mem_blockZ hmN hz
  have e : m * v * m⁻¹ = (m * v₀ * m⁻¹) * (m * (v₀⁻¹ * v) * m⁻¹) := by group
  show H.D.ψe (m * v₀ * m⁻¹) = _
  rw [e, H.D.ψe_mul (conj_mem_blockU hmN hv₀V) (blockZ_le_blockU L hzc),
    (H.D.ψe_eq_zero_iff (blockZ_le_blockU L hzc)).2 hzc, add_zero]

include H in
theorem act_add {m : G} (hm : m ∈ M) (w w' : Fin 2 → Fq n) :
    act H m (w + w') = act H m w + act H m w' := by
  have hmN : m ∈ Subgroup.normalizer (L : Set G) := H.normal hm
  have h1 : w + w' = H.D.ψe (vecC H w * vecC H w') := by
    rw [H.D.ψe_mul (vecC_mem H w) (vecC_mem H w'), ψe_vecC, ψe_vecC]
  have e : m * (vecC H w * vecC H w') * m⁻¹ =
      (m * vecC H w * m⁻¹) * (m * vecC H w' * m⁻¹) := by group
  rw [h1, act_vec H hm (mul_mem (vecC_mem H w) (vecC_mem H w')), e,
    H.D.ψe_mul (conj_mem_blockU hmN (vecC_mem H w)) (conj_mem_blockU hmN (vecC_mem H w'))]
  rfl

include H in
theorem act_one (w : Fin 2 → Fq n) : act H 1 w = w := by
  unfold act
  rw [one_mul, inv_one, mul_one, ψe_vecC]

include H in
theorem act_mul {m m' : G} (hm : m ∈ M) (hm' : m' ∈ M) (w : Fin 2 → Fq n) :
    act H (m * m') w = act H m (act H m' w) := by
  have hm'N : m' ∈ Subgroup.normalizer (L : Set G) := H.normal hm'
  have h1 : act H m' w = H.D.ψe (m' * vecC H w * m'⁻¹) := rfl
  rw [h1, act_vec H hm (conj_mem_blockU hm'N (vecC_mem H w))]
  unfold act
  congr 1
  group

include H in
theorem act_inv_act {m : G} (hm : m ∈ M) (w : Fin 2 → Fq n) :
    act H m⁻¹ (act H m w) = w := by
  rw [← act_mul H (M.inv_mem hm) hm, inv_mul_cancel, act_one]

include H in
theorem act_act_inv {m : G} (hm : m ∈ M) (w : Fin 2 → Fq n) :
    act H m (act H m⁻¹ w) = w := by
  rw [← act_mul H hm (M.inv_mem hm), mul_inv_cancel, act_one]

@[expose] noncomputable def actPerm (m : ↥M) : Equiv.Perm (Fin 2 → Fq n) where
  toFun := act H m
  invFun := act H (m : G)⁻¹
  left_inv w := act_inv_act H m.2 w
  right_inv w := act_act_inv H m.2 w

@[expose] noncomputable def actHom : ↥M →* Equiv.Perm (Fin 2 → Fq n) where
  toFun := actPerm H
  map_one' := Equiv.ext fun w => act_one H w
  map_mul' m m' := Equiv.ext fun w => act_mul H m.2 m'.2 w

theorem actHom_apply (m : ↥M) (w : Fin 2 → Fq n) : actHom H m w = act H m w := rfl

theorem actHom_add (m : ↥M) (w w' : Fin 2 → Fq n) :
    actHom H m (w + w') = actHom H m w + actHom H m w' := act_add H m.2 w w'

theorem act_L {l : G} (hl : l ∈ L) (w : Fin 2 → Fq n) :
    act H l w = ((H.D.φ ⟨l, hl⟩ : Matrix.SpecialLinearGroup (Fin 2) (Fq n)) :
      Matrix (Fin 2) (Fin 2) (Fq n)).mulVec w := by
  unfold act
  rw [H.D.ψe_conj hl (vecC_mem H w), ψe_vecC]

theorem actHom_L (l : ↥L) : actHom H ⟨l, H.le l.2⟩ = slPerm (Fq n) (H.D.φ l) := by
  refine Equiv.ext fun w => ?_
  rw [actHom_apply, slPerm_apply, Matrix.SpecialLinearGroup.smul_def]
  exact act_L H l.2 w

theorem normalizes (m : ↥M) (g : Matrix.SpecialLinearGroup (Fin 2) (Fq n)) :
    ∃ g' : Matrix.SpecialLinearGroup (Fin 2) (Fq n),
      (actHom H m)⁻¹ * slPerm (Fq n) g * actHom H m = slPerm (Fq n) g' := by
  set l : ↥L := H.D.sec g with hl
  have hm' : (m : G)⁻¹ * (l : G) * (m : G) ∈ L := by
    have := (Subgroup.mem_normalizer_iff.1 (H.normal (M.inv_mem m.2)) (l : G)).1 l.2
    simpa using this
  refine ⟨H.D.φ ⟨(m : G)⁻¹ * (l : G) * (m : G), hm'⟩, ?_⟩
  rw [← actHom_L H ⟨(m : G)⁻¹ * (l : G) * (m : G), hm'⟩]
  have e1 : (⟨(m : G)⁻¹ * (l : G) * (m : G), H.le hm'⟩ : ↥M) =
      m⁻¹ * ⟨(l : G), H.le l.2⟩ * m := Subtype.ext (by simp)
  have e2 : slPerm (Fq n) g = actHom H ⟨(l : G), H.le l.2⟩ := by
    rw [actHom_L, hl, H.D.φ_sec]
  rw [e2, e1, map_mul, map_mul, map_inv]

theorem exists_sigma (m : ↥M) : ∃ σ : Fq n ≃+* Fq n, IsSemilinearWith (actHom H m) σ :=
  exists_isSemilinearWith_of_normalizes (actHom H m) (actHom_add H m) (normalizes H m)

@[expose] noncomputable def sigma (m : ↥M) : Fq n ≃+* Fq n := Classical.choose (exists_sigma H m)

theorem isSemilinear_sigma (m : ↥M) : IsSemilinearWith (actHom H m) (sigma H m) :=
  Classical.choose_spec (exists_sigma H m)

theorem sigma_unique {m : ↥M} {σ : Fq n ≃+* Fq n} (h : IsSemilinearWith (actHom H m) σ) :
    σ = sigma H m :=
  h.unique (isSemilinear_sigma H m)

@[expose] noncomputable def chi : ↥M →* (Fq n ≃+* Fq n) where
  toFun := sigma H
  map_one' := by
    symm
    exact sigma_unique H (m := 1) (by rw [map_one]; exact IsSemilinearWith.one_perm)
  map_mul' a b := by
    symm
    exact sigma_unique H (m := a * b)
      (by rw [map_mul]; exact (isSemilinear_sigma H a).mul (isSemilinear_sigma H b))

theorem isSemilinear_chi (m : ↥M) : IsSemilinearWith (actHom H m) (chi H m) :=
  isSemilinear_sigma H m

theorem chi_eq_one_iff (m : ↥M) :
    chi H m = 1 ↔ IsSemilinearWith (actHom H m) (1 : Fq n ≃+* Fq n) :=
  ⟨fun h => h ▸ isSemilinear_chi H m, fun h => (sigma_unique H h).symm⟩

theorem chi_of_mem_L {l : G} (hl : l ∈ L) : chi H ⟨l, H.le hl⟩ = 1 := by
  refine (chi_eq_one_iff H _).2 ?_
  have := actHom_L H ⟨l, hl⟩
  rw [this, slPerm_eq_semilinPerm]
  exact semilinPerm_isSemilinear _ _


theorem act_of_mem_cenW {x : G} (hx : x ∈ cenW L M) : ∃ a : Fq n, ∀ w, act H x w = a • w := by
  obtain ⟨hxM, hxN, hxc⟩ := mem_cenW.1 hx
  obtain ⟨a, ha⟩ := H.D.exists_scalar hxN (fun l => hxc l l.2)
  refine ⟨a, fun w => ?_⟩
  have h1 := ha ⟨vecC H w, vecC_mem H w⟩
  have h2 := congrArg Multiplicative.toAdd h1
  simp only [toAdd_ofAdd] at h2
  have h3 : H.D.ψe (x * vecC H w * x⁻¹) = a • w := by
    rw [H.D.ψe_of_mem (conj_mem_blockU hxN (vecC_mem H w))]
    have h4 : Multiplicative.toAdd (H.D.ψ ⟨vecC H w, vecC_mem H w⟩) = w := by
      rw [← H.D.ψe_of_mem (vecC_mem H w), ψe_vecC]
    rw [h4] at h2
    exact h2
  exact h3

theorem chi_of_mem_cenW {x : G} (hx : x ∈ cenW L M) : chi H ⟨x, cenW_le hx⟩ = 1 := by
  obtain ⟨a, ha⟩ := act_of_mem_cenW H hx
  refine (chi_eq_one_iff H _).2 fun c w => ?_
  show act H x (c • w) = c • act H x w
  rw [ha, ha, smul_comm]

theorem mem_cenW_of_actHom_eq_one {x : G} (hxM : x ∈ M) (h1 : actHom H ⟨x, hxM⟩ = 1) :
    x ∈ cenW L M := by
  have hxN : x ∈ Subgroup.normalizer (L : Set G) := H.normal hxM
  have htriv : ∀ v : ↥(blockU L), H.D.ψ (conjU hxN v) = H.D.ψ v := by
    intro v
    have h2 : act H x (H.D.ψe v) = H.D.ψe v := by
      have := congrArg (fun p : Equiv.Perm (Fin 2 → Fq n) => p (H.D.ψe v)) h1
      simpa [actHom_apply] using this
    rw [act_vec H hxM v.2] at h2
    have h3 : (H.D.ψ (conjU hxN v) : Multiplicative (Fin 2 → Fq n)) =
        Multiplicative.ofAdd (H.D.ψe (x * v * x⁻¹)) := by
      rw [H.D.ψe_of_mem (conj_mem_blockU hxN v.2), ofAdd_toAdd]
      rfl
    rw [h3, h2, H.D.ψe_of_mem v.2, ofAdd_toAdd]
  exact mem_cenW.2 ⟨hxM, hxN, fun l hl => H.D.comm_mem_oTwoIn hxN htriv ⟨l, hl⟩⟩

theorem mem_K_of_chi_eq_one {x : G} (hxM : x ∈ M) {k : ℕ} (hk : x ^ 2 ^ k = 1)
    (hχ : chi H ⟨x, hxM⟩ = 1) : x ∈ L ⊔ cenW L M := by
  set m : ↥M := ⟨x, hxM⟩ with hm
  set π := actHom H m with hπ
  have hlin : IsSemilinearWith π (1 : Fq n ≃+* Fq n) := (chi_eq_one_iff H m).1 hχ
  have hadd : ∀ w w' : Fin 2 → Fq n, π (w + w') = π w + π w' := actHom_add H m
  have hMv : ∀ w, (columnMat π).mulVec w = π w := fun w => by
    have := columnMat_mulVec hadd hlin w
    simpa using this
  have hdetpow : ∀ j : ℕ, columnDet (π ^ j) = columnDet π ^ j := by
    intro j
    induction j with
    | zero => simp [columnDet_one]
    | succ j ih =>
      rw [pow_succ', columnDet_mul hadd hlin (π ^ j)]
      have h1 : ∀ x : Fq n, (1 : Fq n ≃+* Fq n) x = x := fun x => rfl
      rw [h1, ih, pow_succ']
  have hmk : m ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
  have hπpow : π ^ 2 ^ k = 1 := by rw [hπ, ← map_pow, hmk, map_one]
  have hdet1 : columnDet π = 1 := by
    apply eq_one_of_pow_two_pow_eq_one (k := k)
    rw [← hdetpow, hπpow, columnDet_one]
  have hdet : (columnMat π).det = 1 := by rw [det_columnMat, hdet1]
  set g : Matrix.SpecialLinearGroup (Fin 2) (Fq n) := ⟨columnMat π, hdet⟩ with hg
  have hslπ : slPerm (Fq n) g = π := by
    refine Equiv.ext fun w => ?_
    rw [slPerm_apply, Matrix.SpecialLinearGroup.smul_def]
    exact hMv w
  obtain ⟨l, hl⟩ := H.D.φ_surj g
  have hπl : actHom H ⟨(l : G), H.le l.2⟩ = π := by rw [actHom_L, hl, hslπ]
  have hq : actHom H ((⟨(l : G), H.le l.2⟩ : ↥M)⁻¹ * m) = 1 := by
    rw [map_mul, map_inv, hπl, inv_mul_cancel]
  have hcen := mem_cenW_of_actHom_eq_one H (M.mul_mem (M.inv_mem (H.le l.2)) hxM) hq
  have e : x = (l : G) * ((l : G)⁻¹ * x) := by group
  rw [e]
  exact Subgroup.mul_mem_sup l.2 hcen

end Chi


section Sec4Form

open CFSG.CGT.PushingUpLit.T2KR

variable {L M T : Subgroup G} {n : ℕ}

theorem comm_mem_Rl_sup_Dc (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple) :
    ∀ x ∈ T, ∀ y ∈ T, ⁅x, y⁆ ∈ Rl L T ⊔ Dc L T := by
  have h : NatBlock L n := hs.hyp.natBlock
  have hLM : L ≤ M := hs.hyp.le
  have hMN : M ≤ Subgroup.normalizer (L : Set G) := hs.hyp.normal hE1
  let H : CoordData G L M n := ⟨h.natData, h, hLM, hMN⟩
  intro x hx y hy
  have hcT : ⁅x, y⁆ ∈ T := Aux.comm_mem_subgroup hx hy
  have hcM : ⁅x, y⁆ ∈ M := hs.sylow.le hcT
  have hχ : chi H ⟨⁅x, y⁆, hcM⟩ = 1 := by
    have e : (⟨⁅x, y⁆, hcM⟩ : ↥M) = ⁅(⟨x, hs.sylow.le hx⟩ : ↥M), ⟨y, hs.sylow.le hy⟩⁆ := rfl
    rw [e, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact ringEquiv_mul_comm n _ _
  obtain ⟨k, hk⟩ := hs.sylow.isPGroup ⟨⁅x, y⁆, hcT⟩
  have hk' : ⁅x, y⁆ ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hK := mem_K_of_chi_eq_one H hcM hk' hχ
  rw [← inf_sup_cenW h hLM hMN hs.sylow]
  exact ⟨hcT, hK⟩

theorem le_normalizer_of_Rl_sup_Dc_le (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple)
    {X : Subgroup G} (hT₁X : Rl L T ⊔ Dc L T ≤ X) (hXT : X ≤ T) :
    T ≤ Subgroup.normalizer (X : Set G) := by
  have key : ∀ t ∈ T, ∀ y ∈ X, t * y * t⁻¹ ∈ X := by
    intro t ht y hy
    have h1 : ⁅t, y⁆ ∈ X := hT₁X (comm_mem_Rl_sup_Dc hs hE1 t ht y (hXT hy))
    have e : t * y * t⁻¹ = ⁅t, y⁆ * y := by simp [commutatorElement_def]
    rw [e]
    exact X.mul_mem h1 hy
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key t ht y, fun hy => ?_⟩
  have := key t⁻¹ (T.inv_mem ht) _ hy
  simpa [mul_assoc] using this

theorem mem_of_le_map_conj_sec4 (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple)
    (hA78 : Aschbacher78OneGen) {y : G}
    (hy : Rl L T ⊔ Dc L T ≤ M.map (MulAut.conj y).toMonoidHom) : y ∈ M := by
  have hMN : M ≤ Subgroup.normalizer (L : Set G) := hs.hyp.normal hE1
  refine mem_of_le_map_conj hs.sylow hs.N_T (sup_le Rl_le_T Dc_le_T)
    (fun X h1 h2 => le_normalizer_of_Rl_sup_Dc_le hs hE1 h1 h2) (fun X h1 h2 => ?_) hy
  rcases hA78 G L M n hs.hyp hMN T X hs.sylow h2 h1 with h | h
  · exact h
  · exact absurd h hs.noG4

theorem mem_of_le_normalizer_map_conj (hs : Sec4 G L M T n) (hE1 : FooteNonsolvableSimple)
    (hA78 : Aschbacher78OneGen) {A : Subgroup G} (hAN : Subgroup.normalizer (A : Set G) ≤ M)
    {g : G}
    (hB : Rl L T ⊔ Dc L T ≤
      Subgroup.normalizer ((A.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)) :
    g ∈ M := by
  refine mem_of_le_map_conj_sec4 hs hE1 hA78 fun t ht => ?_
  rw [mem_map_conj_iff]
  apply hAN
  rw [Subgroup.mem_normalizer_iff]
  intro a
  have h1 := Subgroup.mem_normalizer_iff.1 (hB ht) (g * a * g⁻¹)
  rw [mem_map_conj_iff, mem_map_conj_iff] at h1
  have e1 : g⁻¹ * (g * a * g⁻¹) * g = a := by group
  have e2 : g⁻¹ * (t * (g * a * g⁻¹) * t⁻¹) * g = (g⁻¹ * t * g) * a * (g⁻¹ * t * g)⁻¹ := by
    group
  rw [e1, e2] at h1
  exact h1

end Sec4Form

end WeakCl

end CFSG.CGT.PushingUpLit.T2KSW
