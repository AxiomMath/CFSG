module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinGen
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinA7Data
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2

public section

namespace CFSG.QuasithinUnique.Unc25G2

namespace A7

open Equiv

abbrev A : Type := alternatingGroup (Fin 7)

structure LG where
  elts : List (Perm (Fin 7))
  one_mem : (1 : Perm (Fin 7)) ∈ elts
  mul_mem : ∀ x ∈ elts, ∀ y ∈ elts, x * y ∈ elts
  inv_mem : ∀ x ∈ elts, x⁻¹ ∈ elts

@[expose] def LG.sub (T : LG) : Subgroup A where
  carrier := {x | (x : Perm (Fin 7)) ∈ T.elts}
  mul_mem' := fun {_ _} hx hy => T.mul_mem _ hx _ hy
  one_mem' := T.one_mem
  inv_mem' := fun {_} hx => T.inv_mem _ hx

theorem LG.card_sub (T : LG) (hev : ∀ σ ∈ T.elts, Perm.sign σ = 1) :
    Nat.card T.sub = T.elts.toFinset.card := by
  rw [← Nat.card_eq_finsetCard]
  apply Nat.card_congr
  exact
    { toFun := fun x => ⟨(x : A).1, List.mem_toFinset.mpr x.2⟩
      invFun := fun σ => ⟨⟨σ.1, Equiv.Perm.mem_alternatingGroup.mpr
        (hev _ (List.mem_toFinset.mp σ.2))⟩, List.mem_toFinset.mp σ.2⟩
      left_inv := fun x => rfl
      right_inv := fun σ => rfl }

@[expose] def P0A
    : Subgroup A := (LG.mk P0l a7_facts.oneP a7_facts.mulP a7_facts.invP).sub

@[expose] def V0A
    : Subgroup A := (LG.mk V0l a7_facts.oneV a7_facts.mulV a7_facts.invV).sub

@[expose] def K1A
    : Subgroup A := (LG.mk K1l a7_facts.oneK a7_facts.mulK a7_facts.invK).sub

@[expose] def T0A
    : Subgroup A := (LG.mk T0l a7_facts.oneT a7_facts.mulT a7_facts.invT).sub

theorem card_P0A : Nat.card P0A = 8 :=
  (LG.card_sub _ a7_facts.evP).trans a7_facts.cardP

theorem card_V0A : Nat.card V0A = 4 :=
  (LG.card_sub _ a7_facts.evV).trans a7_facts.cardV

theorem card_K1A : Nat.card K1A = 24 :=
  (LG.card_sub _ a7_facts.evK).trans a7_facts.cardK

theorem V0A_le_P0A : V0A ≤ P0A := fun _ hx => a7_facts.VP _ hx

theorem P0A_le_K1A : P0A ≤ K1A := fun _ hx => a7_facts.PK _ hx

@[expose] def aA
    : A := ⟨aP, Equiv.Perm.mem_alternatingGroup.mpr a7_facts.evGens.1⟩

@[expose] def bA
    : A := ⟨bP, Equiv.Perm.mem_alternatingGroup.mpr a7_facts.evGens.2.1⟩

@[expose] def c1A
    : A := ⟨c1P, Equiv.Perm.mem_alternatingGroup.mpr a7_facts.evGens.2.2.1⟩

@[expose] def c2A
    : A := ⟨c2P, Equiv.Perm.mem_alternatingGroup.mpr a7_facts.evGens.2.2.2⟩

theorem aA_mem : aA ∈ V0A := a7_facts.aV

theorem bA_mem : bA ∈ V0A := a7_facts.bV

theorem aA_ne
    : aA ≠ 1 := fun h => a7_facts.aNe (congrArg Subtype.val h)

theorem bA_ne
    : bA ≠ 1 := fun h => a7_facts.bNe (congrArg Subtype.val h)

theorem ab_ne
    : aA ≠ bA := fun h => a7_facts.abNe (congrArg Subtype.val h)

theorem ab_comm : aA * bA = bA * aA := Subtype.ext a7_facts.abComm

theorem aa_eq : aA * aA = 1 := Subtype.ext a7_facts.aaEq

theorem bb_eq : bA * bA = 1 := Subtype.ext a7_facts.bbEq

theorem c2_ne
    : c2A ≠ 1 := fun h => a7_facts.c2Ne (congrArg Subtype.val h)

theorem c2_cube : c2A ^ 3 = 1 := Subtype.ext a7_facts.c2Cube

theorem c1_ne
    : c1A ≠ 1 := fun h => a7_facts.c1Ne (congrArg Subtype.val h)

theorem c1_cube : c1A ^ 3 = 1 := Subtype.ext a7_facts.c1Cube

theorem c2a_comm
    : c2A * aA = aA * c2A := Subtype.ext a7_facts.c2aComm

theorem c2b_comm
    : c2A * bA = bA * c2A := Subtype.ext a7_facts.c2bComm

theorem c1_mem : c1A ∈ K1A := a7_facts.c1K

theorem c1_not_mem : c1A ∉ T0A := a7_facts.c1T

theorem V0A_elem
    {v : A} (hv : v ∈ V0A) : v = 1 ∨ v = aA ∨ v = bA ∨ v = aA * bA := by
  have h : (v : Perm (Fin 7)) ∈ V0l := hv
  simp only [V0l, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Or.inl (Subtype.ext h))
  · exact Or.inr (Or.inr (Or.inl (Subtype.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Subtype.ext h)))

theorem T0A_elem
    {t : A} (ht : t ∈ T0A) : t = 1 ∨ t = c2A ∨ t = c2A * c2A := by
  have h : (t : Perm (Fin 7)) ∈ T0l := ht
  simp only [T0l, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Or.inl (Subtype.ext h))
  · exact Or.inr (Or.inr (Subtype.ext h))

theorem klein_A
    {u₁ u₂ : A} (h₁ : u₁ ∈ P0A) (h₂ : u₂ ∈ P0A) (n₁ : u₁ ≠ 1) (n₂ : u₂ ≠ 1)
    (n₁₂ : u₁ ≠ u₂) (hc : u₁ * u₂ = u₂ * u₁) (s₁ : u₁ * u₁ = 1) (s₂ : u₂ * u₂ = 1) {x : A}
    (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1) (hxc₁ : x * u₁ = u₁ * x) (hxc₂ : x * u₂ = u₂ * x) :
    u₁ ∈ V0A ∧ u₂ ∈ V0A :=
  a7_facts.klein _ h₁ _ h₂ (fun h => n₁ (Subtype.ext h)) (fun h => n₂ (Subtype.ext h))
    (fun h => n₁₂ (Subtype.ext h)) (congrArg Subtype.val hc) (congrArg Subtype.val s₁)
    (congrArg Subtype.val s₂)
    ⟨x, Equiv.Perm.mem_alternatingGroup.mp x.2, fun h => hx1 (Subtype.ext h),
      congrArg Subtype.val hx3, congrArg Subtype.val hxc₁, congrArg Subtype.val hxc₂⟩

theorem T0char_A
    {x : A} (hx3 : x ^ 3 = 1) (hc : ∀ v ∈ V0A, x * v = v * x) : x ∈ T0A :=
  a7_facts.T0char _ (Equiv.Perm.mem_alternatingGroup.mp x.2) (congrArg Subtype.val hx3)
    (fun v hv => congrArg Subtype.val
      (hc ⟨v, Equiv.Perm.mem_alternatingGroup.mpr (a7_facts.evV v hv)⟩ hv))

theorem Tconj_A
    {y : A} (hy : y ∈ T0A) (hy1 : y ≠ 1) : ∃ g : A, g * c2A * g⁻¹ = y := by
  obtain ⟨g, hg, hgy⟩ := a7_facts.Tconj _ hy (fun h => hy1 (Subtype.ext h))
  exact ⟨⟨g, Equiv.Perm.mem_alternatingGroup.mpr hg⟩, Subtype.ext hgy⟩

theorem c1conj_A : ∃ g : A, g * c2A * g⁻¹ = c1A := by
  obtain ⟨g, hg, hgy⟩ := a7_facts.c1conj
  exact ⟨⟨g, Equiv.Perm.mem_alternatingGroup.mpr hg⟩, Subtype.ext hgy⟩

theorem three_A
    {y : A} (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) (hn : ∀ v ∈ V0A, y * v * y⁻¹ ∈ V0A)
    (hT : y ∉ T0A) (hg : ∃ g : A, g * c2A * g⁻¹ = y) : y ∈ K1A := by
  obtain ⟨g, hg⟩ := hg
  refine a7_facts.three _ (Equiv.Perm.mem_alternatingGroup.mp y.2) (congrArg Subtype.val hy3)
    (fun h => hy1 (Subtype.ext h)) ?_ hT
    ⟨g, Equiv.Perm.mem_alternatingGroup.mp g.2, congrArg Subtype.val hg⟩
  intro v hv
  exact hn ⟨v, Equiv.Perm.mem_alternatingGroup.mpr (a7_facts.evV v hv)⟩ hv

theorem Vnorm_A
    {k v : A} (hk : k ∈ K1A) (hv : v ∈ V0A) : k * v * k⁻¹ ∈ V0A :=
  a7_facts.Vnorm _ hk _ hv

theorem Vcent_A
    {k : A} (hk : k ∈ K1A) (hc : ∀ v ∈ V0A, k * v = v * k) : k ∈ V0A :=
  a7_facts.Vcent _ hk (fun v hv => congrArg Subtype.val
    (hc ⟨v, Equiv.Perm.mem_alternatingGroup.mpr (a7_facts.evV v hv)⟩ hv))

theorem notnormP_A : ∃ k ∈ K1A, ∃ p ∈ P0A, k * p * k⁻¹ ∉ P0A := by
  obtain ⟨k, hk, p, hp, h⟩ := a7_facts.notnormP
  exact ⟨⟨k, Equiv.Perm.mem_alternatingGroup.mpr (a7_facts.evK k hk)⟩, hk,
    ⟨p, Equiv.Perm.mem_alternatingGroup.mpr (a7_facts.evP p hp)⟩, hp, h⟩

theorem tau_A {τ : Perm (Fin 7)} (h2 : τ ^ 2 = 1)
    (h1 : (Finset.univ.filter fun i => τ i = i).card = 1) :
    ∃ k ∈ K1A, (k : Perm (Fin 7)) * τ ≠ τ * (k : Perm (Fin 7)) := by
  obtain ⟨k, hk, hne⟩ := a7_facts.tau τ h2 h1
  exact ⟨⟨k, Equiv.Perm.mem_alternatingGroup.mpr (a7_facts.evK k hk)⟩, hk, hne⟩

theorem map_K1_eq (α : MulAut A) (hα : P0A.map α.toMonoidHom = P0A) :
    K1A.map α.toMonoidHom = K1A := by
  have hαP : ∀ x ∈ P0A, α x ∈ P0A := fun x hx => by
    rw [← hα]; exact ⟨x, hx, rfl⟩
  have hαne : ∀ x : A, x ≠ 1 → α x ≠ 1 := fun x hx h => hx (α.injective (by rw [h, map_one]))
  have hAB : α aA ∈ V0A ∧ α bA ∈ V0A := by
    refine klein_A (hαP _ (V0A_le_P0A aA_mem)) (hαP _ (V0A_le_P0A bA_mem)) (hαne _ aA_ne)
      (hαne _ bA_ne) (fun h => ab_ne (α.injective h)) ?_ ?_ ?_ (x := α c2A) (hαne _ c2_ne) ?_ ?_ ?_
    · rw [← map_mul, ← map_mul, ab_comm]
    · rw [← map_mul, aa_eq, map_one]
    · rw [← map_mul, bb_eq, map_one]
    · rw [← map_pow, c2_cube, map_one]
    · rw [← map_mul, ← map_mul, c2a_comm]
    · rw [← map_mul, ← map_mul, c2b_comm]
  have hVsub : ∀ v ∈ V0A, α v ∈ V0A := by
    intro v hv
    rcases V0A_elem hv with rfl | rfl | rfl | rfl
    · rw [map_one]; exact V0A.one_mem
    · exact hAB.1
    · exact hAB.2
    · rw [map_mul]; exact V0A.mul_mem hAB.1 hAB.2
  have hV : V0A.map α.toMonoidHom = V0A := map_eq_of_forall_mem α hVsub
  have hc2V : ∀ v ∈ V0A, c2A * v = v * c2A := by
    intro v hv
    rcases V0A_elem hv with rfl | rfl | rfl | rfl
    · simp
    · exact c2a_comm
    · exact c2b_comm
    · rw [← mul_assoc, c2a_comm, mul_assoc, c2b_comm, ← mul_assoc]
  have hαc2T : α c2A ∈ T0A := by
    apply T0char_A
    · rw [← map_pow, c2_cube, map_one]
    · intro v hv
      rw [← hV] at hv
      obtain ⟨v', hv', rfl⟩ := hv
      show α c2A * α v' = α v' * α c2A
      rw [← map_mul, ← map_mul, hc2V v' hv']
  have hTsub : ∀ t ∈ T0A, α t ∈ T0A := by
    intro t ht
    rcases T0A_elem ht with rfl | rfl | rfl
    · rw [map_one]; exact T0A.one_mem
    · exact hαc2T
    · rw [map_mul]; exact T0A.mul_mem hαc2T hαc2T
  have hT : T0A.map α.toMonoidHom = T0A := map_eq_of_forall_mem α hTsub
  have hy3 : (α c1A) ^ 3 = 1 := by rw [← map_pow, c1_cube, map_one]
  have hy1 : α c1A ≠ 1 := hαne _ c1_ne
  have hyn : ∀ v ∈ V0A, α c1A * v * (α c1A)⁻¹ ∈ V0A := by
    intro v hv
    rw [← hV] at hv
    obtain ⟨v', hv', rfl⟩ := hv
    have : α c1A * α v' * (α c1A)⁻¹ = α (c1A * v' * c1A⁻¹) := by simp [map_mul, map_inv]
    show α c1A * α v' * (α c1A)⁻¹ ∈ V0A
    rw [this]
    exact hVsub _ (Vnorm_A c1_mem hv')
  have hyT : α c1A ∉ T0A := by
    intro h
    rw [← hT] at h
    obtain ⟨t, ht, hty⟩ := h
    have : t = c1A := α.injective hty
    exact c1_not_mem (this ▸ ht)
  have hyc : ∃ g : A, g * c2A * g⁻¹ = α c1A := by
    obtain ⟨g', hg'⟩ := c1conj_A
    obtain ⟨g'', hg''⟩ := Tconj_A hαc2T (hαne _ c2_ne)
    refine ⟨α g' * g'', ?_⟩
    calc α g' * g'' * c2A * (α g' * g'')⁻¹ = α g' * (g'' * c2A * g''⁻¹) * (α g')⁻¹ := by group
      _ = α g' * α c2A * (α g')⁻¹ := by rw [hg'']
      _ = α (g' * c2A * g'⁻¹) := by simp [map_mul, map_inv]
      _ = α c1A := by rw [hg']
  have hyK : α c1A ∈ K1A := three_A hy3 hy1 hyn hyT hyc
  have hP0 : P0A ≤ K1A.map α.toMonoidHom :=
    calc P0A = P0A.map α.toMonoidHom := hα.symm
      _ ≤ K1A.map α.toMonoidHom := Subgroup.map_mono P0A_le_K1A
  have hyKm : α c1A ∈ K1A.map α.toMonoidHom := ⟨c1A, c1_mem, rfl⟩
  set H : Subgroup A := P0A ⊔ Subgroup.zpowers (α c1A) with hH
  have hHK : H ≤ K1A := sup_le P0A_le_K1A ((Subgroup.zpowers_le).mpr hyK)
  have hHm : H ≤ K1A.map α.toMonoidHom := sup_le hP0 ((Subgroup.zpowers_le).mpr hyKm)
  have h8 : 8 ∣ Nat.card H := by
    have := Subgroup.card_dvd_of_le (le_sup_left : P0A ≤ H)
    rwa [card_P0A] at this
  have h3 : 3 ∣ Nat.card H := by
    have hmem : α c1A ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    have := orderOf_dvd_natCard (⟨α c1A, hmem⟩ : H)
    rwa [Subgroup.orderOf_mk, orderOf_eq_prime hy3 hy1] at this
  have h24 : Nat.card H = 24 := by
    have hle : Nat.card H ≤ 24 := by
      have := Subgroup.card_le_of_le hHK
      rwa [card_K1A] at this
    have hpos : 0 < Nat.card H := Nat.card_pos
    omega
  have hHeq : H = K1A := Subgroup.eq_of_le_of_card_ge hHK (by rw [card_K1A, h24])
  have hle : K1A ≤ K1A.map α.toMonoidHom := hHeq ▸ hHm
  exact (Subgroup.eq_of_le_of_card_ge hle (Subgroup.card_map_of_injective α.injective).le).symm

theorem P0A_isPGroup
    : IsPGroup 2 P0A := IsPGroup.of_card (n := 3) (by rw [card_P0A]; norm_num)

theorem card_A : Nat.card A = 2520 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

theorem P0A_index_odd : ¬ 2 ∣ P0A.index := by
  have h := P0A.card_mul_index
  rw [card_P0A, card_A] at h
  omega

theorem a7_X
    {X : Type*} [Group X] [Finite X] (ρ : X →* A) (hρ : Function.Surjective ρ)
    (hker : ∀ x, ρ x = 1 ↔ x ∈ Subgroup.center X) (hZc : Nat.card ρ.ker = 1 ∨ Nat.card ρ.ker = 3)
    {P : Subgroup X} (hP : IsPGroup 2 P) (hPmap : P.map ρ = P0A) :
    ∃ K V : Subgroup X, V ≤ K ∧ K ≤ Subgroup.normalizer (V : Set X) ∧ IsPGroup 2 V ∧
      (∀ x ∈ K, (∀ v ∈ V, x * v = v * x) → x ∈ V) ∧ K.map ρ = K1A ∧
      ∀ α : MulAut X, P.map α.toMonoidHom = P → K.map α.toMonoidHom = K := by
  have hZ : ρ.ker ≤ Subgroup.center X := fun x hx => (hker x).mp hx
  have hV2 : IsPGroup 2 V0A := IsPGroup.of_card (n := 2) (by rw [card_V0A]; norm_num)
  refine lift_charTwo' ρ hρ hZ hZc hP hPmap card_P0A card_K1A P0A_le_K1A V0A_le_P0A hV2
    (fun k hk v hv => Vnorm_A hk hv) (fun k hk hc => Vcent_A hk hc) notnormP_A
    (fun α => P.map α.toMonoidHom = P) (fun _ h => h) ?_
  intro α hα
  obtain ⟨α', hα'⟩ := exists_descent_of_center hρ hker α
  have hP0 : P0A.map α'.toMonoidHom = P0A := by
    have hcomp : α'.toMonoidHom.comp ρ = ρ.comp α.toMonoidHom :=
      MonoidHom.ext fun x => (hα' x).symm
    rw [← hPmap, Subgroup.map_map, hcomp, ← Subgroup.map_map, hα]
  exact ⟨α', hα', map_K1_eq α' hP0⟩

end A7

end CFSG.QuasithinUnique.Unc25G2

namespace CFSG.QuasithinUnique

open Equiv CFSG.Open CFSG.Quasithin Unc25G2 Unc25G2.A7

theorem a7Excluded : A7Excluded := by
  intro G _ _ L S₀ ML hL hpart hMLL hS₀2 hS₀N hsyl hS₀ML hall
  obtain ⟨φ, τ, hτ2, hτfix, hMLimg⟩ := hpart
  let ρ₀ : ↥L →* A := φ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hρ₀ : Function.Surjective ρ₀ := φ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker₀ : ∀ x, ρ₀ x = 1 ↔ x ∈ Subgroup.center ↥L := by
    intro x
    show φ (QuotientGroup.mk x) = 1 ↔ _
    rw [map_eq_one_iff φ φ.injective, QuotientGroup.eq_one_iff]
  have hZc₀ : Nat.card (Subgroup.center ↥L) = 1 ∨ Nat.card (Subgroup.center ↥L) = 3 := by
    rcases hL with ⟨⟨e⟩⟩ | ⟨_, hc, _⟩
    · left
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥L)
      have h2 : Nat.card ↥L = Nat.card A := Nat.card_congr e.toEquiv
      have h3 : Nat.card (↥L ⧸ Subgroup.center ↥L) = Nat.card A := Nat.card_congr φ.toEquiv
      rw [h2, h3] at h1
      have hpos : 0 < Nat.card A := Nat.card_pos
      apply Nat.eq_of_mul_eq_mul_left hpos
      rw [mul_one]
      exact h1.symm
    · right; exact hc
  have hP'2 : IsPGroup 2 ((S₀ ⊓ L).subgroupOf L) := isPGroup_inf_subgroupOf L hS₀2
  obtain ⟨a, ha⟩ := exists_conj_comp_map_eq ρ₀ hρ₀ hP'2 hsyl.2.2 P0A_isPGroup P0A_index_odd
  let ρ : ↥L →* A := (MulAut.conj a).toMonoidHom.comp ρ₀
  have hρ : Function.Surjective ρ := (MulAut.conj a).surjective.comp hρ₀
  have hρk : ∀ x, ρ x = a * ρ₀ x * a⁻¹ := fun x => rfl
  have hker : ∀ x, ρ x = 1 ↔ x ∈ Subgroup.center ↥L := by
    intro x
    rw [← hker₀ x]
    show (MulAut.conj a) (ρ₀ x) = 1 ↔ _
    rw [map_eq_one_iff _ (MulAut.conj a).injective]
  have hker' : ρ.ker = Subgroup.center ↥L := by
    ext x; exact hker x
  have hZc : Nat.card ρ.ker = 1 ∨ Nat.card ρ.ker = 3 := by rw [hker']; exact hZc₀
  obtain ⟨K, V, hVK, hn, hV, hC, hKmap, hinv⟩ := a7_X ρ hρ hker hZc hP'2 ha
  obtain ⟨hchar, hnorm⟩ := exists_charTwo_map_of_canonical hS₀N hVK hn hV hC
    (fun s hs => hinv _ (map_conjAut_subgroupOf_eq hS₀N hs))
  have hKML : K.map L.subtype ≤ ML := hall _ (Subgroup.map_subtype_le K) hnorm hchar
  have hKle : ∀ k ∈ K, k ∈ ML.subgroupOf L := fun k hk =>
    Subgroup.mem_subgroupOf.mpr (hKML ⟨k, hk, rfl⟩)
  set τ' : Perm (Fin 7) := (a : Perm (Fin 7)) * τ * (a : Perm (Fin 7))⁻¹ with hτ'
  have h2' : τ' ^ 2 = 1 := by rw [hτ', conj_pow, hτ2, mul_one, mul_inv_cancel]
  have h1' : (Finset.univ.filter fun i => τ' i = i).card = 1 := by
    have e : {i : Fin 7 // τ i = i} ≃ {i : Fin 7 // τ' i = i} :=
      Equiv.subtypeEquiv (a : Perm (Fin 7)) (fun i => by
        simp [hτ'])
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card, ← Nat.card_congr e]
    exact hτfix
  obtain ⟨k₀, hk₀, hne⟩ := tau_A h2' h1'
  rw [← hKmap] at hk₀
  obtain ⟨k, hkK, rfl⟩ := hk₀
  have hmem : ρ₀ k ∈ (Subgroup.centralizer ({τ} : Set (Perm (Fin 7)))).comap (alternatingGroup (Fin 7)).subtype := by
    rw [← hMLimg]
    exact ⟨_, ⟨k, hKle k hkK, rfl⟩, rfl⟩
  have hcomm : (ρ₀ k : Perm (Fin 7)) * τ = τ * (ρ₀ k : Perm (Fin 7)) :=
    (Subgroup.mem_centralizer_iff.mp hmem τ (Set.mem_singleton τ)).symm
  apply hne
  rw [hρk]
  show ((a : Perm (Fin 7)) * (ρ₀ k : Perm (Fin 7)) * (a : Perm (Fin 7))⁻¹) * τ' =
    τ' * ((a : Perm (Fin 7)) * (ρ₀ k : Perm (Fin 7)) * (a : Perm (Fin 7))⁻¹)
  calc (a : Perm (Fin 7)) * (ρ₀ k : Perm (Fin 7)) * (a : Perm (Fin 7))⁻¹ * τ'
      = (a : Perm (Fin 7)) * ((ρ₀ k : Perm (Fin 7)) * τ) * (a : Perm (Fin 7))⁻¹ := by
        rw [hτ']; group
    _ = (a : Perm (Fin 7)) * (τ * (ρ₀ k : Perm (Fin 7))) * (a : Perm (Fin 7))⁻¹ := by rw [hcomm]
    _ = τ' * ((a : Perm (Fin 7)) * (ρ₀ k : Perm (Fin 7)) * (a : Perm (Fin 7))⁻¹) := by
        rw [hτ']; group

end CFSG.QuasithinUnique
