module

public import CFSG.GroupTheory.PCore.PrimeCoreImages
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Lift

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U48

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

theorem pPrimeCore_eq_ker {A B : Type*} [Group A] [Finite A] [Group B] [Finite B] (f : A →* B)
    (hf : Function.Surjective f) (hker : ¬ 3 ∣ Nat.card f.ker)
    (hB : GLAPPrimeCore 3 B = ⊥) : GLAPPrimeCore 3 A = f.ker := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := (CFSG.prime_complement_kernel_core_preimage (p := 3) f hf hker).1
  have hB' : CFSG.pPrimeCore 3 B = ⊥ := hB
  rw [hB', MonoidHom.comap_bot] at this
  exact this.symm

@[expose] noncomputable def pquotEquivOfSurj {A B : Type*} [Group A] [Finite A] [Group B]
    [Finite B] (f : A →* B) (hf : Function.Surjective f) (hker : ¬ 3 ∣ Nat.card f.ker)
    (hB : GLAPPrimeCore 3 B = ⊥) : (A ⧸ GLAPPrimeCore 3 A) ≃* B :=
  (QuotientGroup.quotientMulEquivOfEq (pPrimeCore_eq_ker f hf hker hB)).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)

theorem pPrimeCore_normal_eq_bot {C : Type*} [Group C] [Finite C] (hC : GLAPPrimeCore 3 C = ⊥)
    (S : Subgroup C) [S.Normal] : GLAPPrimeCore 3 ↥S = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hC' : CFSG.pPrimeCore 3 C = ⊥ := hC
  show CFSG.pPrimeCore 3 ↥S = ⊥
  set N : Subgroup ↥S := CFSG.pPrimeCore 3 ↥S with hN
  have hnorm : (N.map S.subtype).Normal := by
    refine ⟨fun n hn c => ?_⟩
    obtain ⟨x, hx, rfl⟩ := hn
    have hmap := Subgroup.characteristic_iff_map_eq.1 (inferInstance : N.Characteristic)
      (MulAut.conjNormal c : MulAut ↥S)
    have hmem : (MulAut.conjNormal c : MulAut ↥S) x ∈ N := by
      rw [← hmap]
      exact Subgroup.mem_map_of_mem _ hx
    refine ⟨_, hmem, ?_⟩
    simp [MulAut.conjNormal_val]
  have hcop : Nat.Coprime 3 (Nat.card (N.map S.subtype)) := by
    rw [Subgroup.card_map_of_injective S.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card
  have hle : N.map S.subtype ≤ CFSG.pPrimeCore 3 C := le_sSup ⟨hnorm, hcop⟩
  rw [hC', le_bot_iff] at hle
  exact (Subgroup.map_eq_bot_iff_of_injective N S.subtype_injective).1 hle

section Core

theorem pPrimeCore_eq_bot_of_ker {C A : Type*} [Group C] [Finite C] [CommGroup A] (ρ : C →* A)
    (hρ : ∀ g, ρ g ^ 9 = 1) (hS : CFSG.Open.IsQuasisimple ↥ρ.ker)
    (hZ : ∀ z ∈ Subgroup.center ↥ρ.ker, z ^ 3 = 1) (h3 : ∃ s : ↥ρ.ker, orderOf s = 3) :
    GLAPPrimeCore 3 C = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  show CFSG.pPrimeCore 3 C = ⊥
  rw [CFSG.pPrimeCore_eq_bot_iff]
  intro N hN hcop
  have hNk : N ≤ ρ.ker := by
    intro n hn
    rw [MonoidHom.mem_ker]
    have h1 : orderOf (ρ n) ∣ Nat.card N := by
      refine (orderOf_map_dvd ρ n).trans ?_
      have h0 : orderOf n = orderOf (⟨n, hn⟩ : N) := Subgroup.orderOf_coe ⟨n, hn⟩
      rw [h0]
      exact orderOf_dvd_natCard _
    have h2 : orderOf (ρ n) ∣ 9 := orderOf_dvd_of_pow_eq_one (hρ n)
    have h9 : Nat.Coprime 9 (Nat.card N) := by
      have := Nat.Coprime.pow_left 2 hcop
      simpa using this
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes h9 h2 h1)
  set N' : Subgroup ↥ρ.ker := N.subgroupOf ρ.ker with hN'
  haveI : N'.Normal := hN.subgroupOf _
  have hcard : Nat.card N' = Nat.card N := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNk).toEquiv
  by_cases htop : N' = ⊤
  · exfalso
    obtain ⟨s, hs⟩ := h3
    have h1 : orderOf s ∣ Nat.card N' := by
      have : s ∈ N' := htop ▸ Subgroup.mem_top s
      have h0 : orderOf s = orderOf (⟨s, this⟩ : N') := (Subgroup.orderOf_coe (⟨s, this⟩ : N')).symm ▸ rfl
      rw [h0]
      exact orderOf_dvd_natCard _
    rw [hs, hcard] at h1
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcop h1
  · have hle := le_center_of_normal_of_isQuasisimple hS (inferInstance : N'.Normal) htop
    rw [Subgroup.eq_bot_iff_forall]
    intro n hn
    have hn' : (⟨n, hNk hn⟩ : ↥ρ.ker) ∈ N' := hn
    have hc3 : (⟨n, hNk hn⟩ : ↥ρ.ker) ^ 3 = 1 := hZ _ (hle hn')
    have hord : orderOf (⟨n, hNk hn⟩ : ↥ρ.ker) ∣ 3 := orderOf_dvd_of_pow_eq_one hc3
    have hord2 : orderOf (⟨n, hNk hn⟩ : ↥ρ.ker) ∣ Nat.card N' := by
      have h0 : orderOf (⟨n, hNk hn⟩ : ↥ρ.ker) = orderOf (⟨⟨n, hNk hn⟩, hn'⟩ : N') :=
        (Subgroup.orderOf_coe (⟨⟨n, hNk hn⟩, hn'⟩ : N')).symm ▸ rfl
      rw [h0]
      exact orderOf_dvd_natCard _
    rw [hcard] at hord2
    have h1 := orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop hord hord2)
    exact congrArg Subtype.val h1

theorem le_ker_of_perfect {C A : Type*} [Group C] [CommGroup A] (ρ : C →* A) (T : Subgroup C)
    (hT : ⁅T, T⁆ = T) : T ≤ ρ.ker := by
  rw [← hT, Subgroup.commutator_le]
  intro a _ b _
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
  exact Commute.all _ _

end Core

section Lay

variable {G : Type} [Group G] [Finite G] {X : Subgroup G} {C : Type} [Group C] [Finite C]

@[expose] def restrictTo (π : ↥X →* C) (S : Subgroup C) {H : Subgroup G} (hHX : H ≤ X)
    (hH : ∀ h : ↥H, π (Subgroup.inclusion hHX h) ∈ S) : ↥H →* ↥S :=
  (π.comp (Subgroup.inclusion hHX)).codRestrict S hH

theorem restrictTo_surjective (π : ↥X →* C) (S : Subgroup C) {H : Subgroup G} (hHX : H ≤ X)
    (hH : ∀ h : ↥H, π (Subgroup.inclusion hHX h) ∈ S)
    (hS : ∀ s ∈ S, ∃ h : ↥H, π (Subgroup.inclusion hHX h) = s) :
    Function.Surjective (restrictTo π S hHX hH) := by
  intro s
  obtain ⟨h, hh⟩ := hS s.1 s.2
  exact ⟨h, Subtype.ext hh⟩

theorem restrictTo_ker (π : ↥X →* C) (S : Subgroup C) {H : Subgroup G} (hHX : H ≤ X)
    (hH : ∀ h : ↥H, π (Subgroup.inclusion hHX h) ∈ S) (hker : ¬ 3 ∣ Nat.card π.ker) :
    ¬ 3 ∣ Nat.card (restrictTo π S hHX hH).ker := by
  intro h3
  apply hker
  refine h3.trans ?_
  rw [← Subgroup.card_map_of_injective (K := (restrictTo π S hHX hH).ker) H.subtype_injective,
    ← Subgroup.card_map_of_injective (K := π.ker) X.subtype_injective]
  apply Subgroup.card_dvd_of_le
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨Subgroup.inclusion hHX x, ?_, rfl⟩
  have := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
  exact MonoidHom.mem_ker.2 this

theorem layer_of_surj (π : ↥X →* C) (hπ : Function.Surjective π) (hker : ¬ 3 ∣ Nat.card π.ker)
    (hC : GLAPPrimeCore 3 C = ⊥) (S : Subgroup C) [S.Normal] (hS : CFSG.Open.IsQuasisimple ↥S)
    (hperf : ∀ T : Subgroup C, ⁅T, T⁆ = T → T ≤ S) :
    ∃ J : Subgroup G, GLAPComponent 3 X J ∧ GLAPLayer 3 X = J ∧
      (J.subgroupOf X).map π = S ∧ Nonempty (PQuot 3 J ≃* ↥S) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSc : GLAPPrimeCore 3 ↥S = ⊥ := pPrimeCore_normal_eq_bot hC S
  set P : Subgroup ↥X := S.comap π with hP
  set Y : Subgroup G := P.map X.subtype with hY
  have hYX : Y ≤ X := Subgroup.map_subtype_le _
  have hYsub : Y.subgroupOf X = P := Subgroup.comap_map_eq_self_of_injective X.subtype_injective P
  have hYsn : IsSubnormal Y X := by
    refine IsSubnormal.step hYX ?_ (IsSubnormal.refl X)
    rw [hYsub]
    exact Subgroup.Normal.comap inferInstance π
  have hYmem : ∀ y : ↥Y, π (Subgroup.inclusion hYX y) ∈ S := by
    intro y
    obtain ⟨x, hx, hxy⟩ := y.2
    have : Subgroup.inclusion hYX y = x := Subtype.ext hxy.symm
    rw [this]; exact hx
  have hYimg : ∀ s ∈ S, ∃ y : ↥Y, π (Subgroup.inclusion hYX y) = s := by
    intro s hs
    obtain ⟨x, hx⟩ := hπ s
    have hxP : x ∈ P := by rw [hP, Subgroup.mem_comap, hx]; exact hs
    exact ⟨⟨x.1, ⟨x, hxP, rfl⟩⟩, hx⟩
  set πY := restrictTo π S hYX hYmem with hπY
  have hπYs : Function.Surjective πY := restrictTo_surjective π S hYX hYmem hYimg
  have hπYk : ¬ 3 ∣ Nat.card πY.ker := restrictTo_ker π S hYX hYmem hker
  have hYq : CFSG.Open.IsQuasisimple (↥Y ⧸ GLAPPrimeCore 3 ↥Y) :=
    hS.of_mulEquiv (pquotEquivOfSurj πY hπYs hπYk hSc)
  obtain ⟨hJ, huniq, hbar⟩ := glaPLayer_of_isQuasisimple (p := 3) hYq
  have hJX : GLAPComponent 3 X (GLAPLayer 3 Y) := glaPComponent_of_isSubnormal' Nat.prime_three hYsn hJ
  have hJY : GLAPLayer 3 Y ≤ Y := hJ.1
  have hJXle : GLAPLayer 3 Y ≤ X := hJY.trans hYX
  have hJimg : ((GLAPLayer 3 Y).subgroupOf X).map π = S := by
    apply le_antisymm
    · rintro _ ⟨j, hj, rfl⟩
      have hjY : (j : G) ∈ Y := hJY (Subgroup.mem_subgroupOf.1 hj)
      obtain ⟨x, hx, hxj⟩ := hjY
      have : x = j := Subtype.ext hxj
      rw [← this]; exact hx
    · intro s hs
      obtain ⟨x, hx⟩ := hπ s
      have hxY : (x : G) ∈ Y := ⟨x, Subgroup.mem_comap.2 (by rw [hx]; exact hs), rfl⟩
      obtain ⟨j, hj, ho⟩ := exists_of_barX_le (p := 3) (X := Y) (J := GLAPLayer 3 Y) (K := Y)
        (by rw [barX_self, hbar]) hxY hxY
      obtain ⟨o', ho', hoeq⟩ := ho
      have hπo : π (Subgroup.inclusion hYX o') = 1 := by
        have h1 : o' ∈ πY.ker := by
          rw [← pPrimeCore_eq_ker πY hπYs hπYk hSc]; exact ho'
        exact congrArg Subtype.val (MonoidHom.mem_ker.1 h1)
      refine ⟨⟨j, hJXle hj⟩, Subgroup.mem_subgroupOf.2 hj, ?_⟩
      have hxe : x = ⟨j, hJXle hj⟩ * Subgroup.inclusion hYX o' :=
        Subtype.ext (by
          show (x : G) = j * (o' : G)
          have h : (o' : G) = j⁻¹ * (x : G) := hoeq
          rw [h]; group)
      show π ⟨j, hJXle hj⟩ = s
      rw [← hx, hxe, map_mul, hπo, mul_one]
  have hJmem : ∀ j : ↥(GLAPLayer 3 Y), π (Subgroup.inclusion hJXle j) ∈ S := fun j =>
    hJimg ▸ ⟨⟨j.1, hJXle j.2⟩, Subgroup.mem_subgroupOf.2 j.2, rfl⟩
  have hJs : Function.Surjective (restrictTo π S hJXle hJmem) := by
    refine restrictTo_surjective π S hJXle hJmem fun s hs => ?_
    obtain ⟨x, hx, rfl⟩ := (hJimg.symm ▸ hs : s ∈ ((GLAPLayer 3 Y).subgroupOf X).map π)
    exact ⟨⟨x.1, Subgroup.mem_subgroupOf.1 hx⟩, rfl⟩
  refine ⟨GLAPLayer 3 Y, hJX, ?_, hJimg, ⟨pquotEquivOfSurj _ hJs
    (restrictTo_ker π S hJXle hJmem hker) hSc⟩⟩
  unfold GLAPLayer
  apply le_antisymm
  · refine sSup_le fun K hK => ?_
    have hbarK := barX_perfect_of_glaPComponent hK
    let ψ := pquotEquivOfSurj π hπ hker hC
    have hT : (K.subgroupOf X).map π = (barX 3 X K).map ψ.toMonoidHom := by
      unfold barX
      rw [Subgroup.map_map]
      rfl
    have hTperf : ⁅(K.subgroupOf X).map π, (K.subgroupOf X).map π⁆ = (K.subgroupOf X).map π := by
      rw [hT, ← Subgroup.map_commutator, hbarK]
    have hTS := hperf _ hTperf
    have hKY : K ≤ Y := by
      intro k hk
      have hkX : k ∈ X := hK.1 hk
      have : π ⟨k, hkX⟩ ∈ S := hTS ⟨⟨k, hkX⟩, Subgroup.mem_subgroupOf.2 hk, rfl⟩
      exact ⟨⟨k, hkX⟩, this, rfl⟩
    have hKY' : GLAPComponent 3 Y K := glaPComponent_of_le Nat.prime_three hK hKY hYX
    exact (huniq K hKY').le
  · exact le_sSup hJX

theorem pPrimeCore_eq_bot_of_simple {W : Type*} [Group W] [Finite W] [IsSimpleGroup W]
    (h3 : 3 ∣ Nat.card W) : GLAPPrimeCore 3 W = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  show CFSG.pPrimeCore 3 W = ⊥
  rw [CFSG.pPrimeCore_eq_bot_iff]
  intro N hN hcop
  haveI := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · exfalso
    rw [h, Subgroup.card_top] at hcop
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcop h3

theorem layer_ne_bot_of_normal_simple {Y W : Subgroup G} (hWY : W ≤ Y)
    (hn : (W.subgroupOf Y).Normal) [IsSimpleGroup ↥W] (hna : ¬ IsMulCommutative ↥W)
    (h3 : 3 ∣ Nat.card W) : GLAPLayer 3 Y ≠ ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hO : GLAPPrimeCore 3 ↥W = ⊥ := pPrimeCore_eq_bot_of_simple h3
  have hq : CFSG.Open.IsQuasisimple ↥W := isQuasisimple_of_simple_nonabelian hna
  have hWq : CFSG.Open.IsQuasisimple (↥W ⧸ GLAPPrimeCore 3 ↥W) :=
    hq.of_mulEquiv ((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot)
  obtain ⟨hD, -, -⟩ := glaPLayer_of_isQuasisimple (p := 3) hWq
  have hsn : IsSubnormal W Y := IsSubnormal.step hWY hn (IsSubnormal.refl Y)
  have hDY : GLAPComponent 3 Y (GLAPLayer 3 W) := glaPComponent_of_isSubnormal' Nat.prime_three hsn hD
  intro hbot
  have hle : GLAPLayer 3 W ≤ GLAPLayer 3 Y := by
    unfold GLAPLayer
    exact le_sSup hDY
  rw [hbot, le_bot_iff] at hle
  have hnt : Nontrivial ↥(barX 3 W (GLAPLayer 3 W)) := isQuasisimple_nontrivial hD.2.2.1.2.2
  rw [hle] at hnt
  have hb : barX 3 W ⊥ = ⊥ := by
    unfold barX
    simp
  rw [hb] at hnt
  haveI : Subsingleton ↥(⊥ : Subgroup (↥W ⧸ GLAPPrimeCore 3 ↥W)) := inferInstance
  exact not_nontrivial_iff_subsingleton.2 this hnt

end Lay

end CFSG.LocalAnalysis.GLTheoremA.CatB.U48
