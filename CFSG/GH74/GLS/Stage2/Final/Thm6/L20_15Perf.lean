module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L20_15Two
public import CFSG.GroupTheory.ThompsonIndexTwo
public import CFSG.LocalAnalysis.ZStar.BrauerSuzukiShortcut

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L20

open Subgroup CFSG

section Perfect

variable {X : Type} [Group X]

theorem not_normal_index_two_of_perfect (hperf : commutator X = ⊤) {N : Subgroup X} (hN : N.Normal)
    (hi : N.index = 2) : False := by
  have hle : commutator X ≤ N := by
    rw [commutator_def]
    refine Subgroup.commutator_le.mpr fun g _ h _ => ?_
    rw [commutatorElement_def]
    rw [Subgroup.mul_mem_iff_of_index_two hi, inv_mem_iff]
    have h1 : g * h * g⁻¹ ∈ N ↔ h ∈ N := by
      constructor
      · intro hh
        have := hN.conj_mem _ hh g⁻¹
        simpa [mul_assoc] using this
      · intro hh
        exact hN.conj_mem _ hh g
    exact h1
  rw [hperf] at hle
  have : N = ⊤ := top_le_iff.mp hle
  rw [this, Subgroup.index_top] at hi
  omega

variable [Finite X]

theorem exists_conj_mem_sylow {P : Subgroup X} (hP : IsPGroup 2 P) (hPidx : ¬ 2 ∣ P.index) {a : X}
    (ha2 : a * a = 1) : ∃ g : X, g * a * g⁻¹ ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Sylow 2 X := hP.toSylow hPidx
  have hord : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact ha2)
  have hz : IsPGroup 2 (zpowers a) := by
    refine IsPGroup.of_card (n := if orderOf a = 1 then 0 else 1) ?_
    rw [Nat.card_zpowers]
    rcases (Nat.dvd_prime Nat.prime_two).mp hord with h | h
    · simp [h]
    · simp [h]
  obtain ⟨Q, hQ⟩ := hz.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X Q S
  refine ⟨g, ?_⟩
  have hsm : g * a * g⁻¹ ∈ (g • Q : Sylow 2 X) := (Sylow.equivSMul Q g ⟨a, hQ (Subgroup.mem_zpowers a)⟩).property
  rw [hg] at hsm
  exact hsm


theorem single_class_of_perfect (hperf : commutator X = ⊤) {P M : Subgroup X} (hP : IsPGroup 2 P)
    (hPidx : ¬ 2 ∣ P.index) (hMP : M ≤ P) (hMc : IsCyclic M) (hMi : M.relIndex P ≤ 2) {a b : X}
    (ha2 : a * a = 1) (hb2 : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : IsConj a b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMc' := hMc
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := M)
  have hMz : ∀ m ∈ M, m ∈ zpowers (g : X) := by
    intro m hm
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨m, hm⟩)
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hord2 : ∀ v : X, v * v = 1 → v ≠ 1 → orderOf v = 2 := fun v hv2 hv1 =>
    orderOf_eq_prime (by rw [sq]; exact hv2) hv1
  have key : ∀ v : X, v * v = 1 → v ≠ 1 → ∃ m ∈ M, m * m = 1 ∧ m ≠ 1 ∧ IsConj v m := by
    intro v hv2 hv1
    obtain ⟨h, hh⟩ := exists_conj_mem_sylow hP hPidx hv2
    set v' := h * v * h⁻¹ with hv'
    have hv'2 : v' * v' = 1 := by
      calc v' * v' = h * (v * v) * h⁻¹ := by simp only [hv']; group
        _ = 1 := by rw [hv2]; group
    have hv'1 : v' ≠ 1 := by
      intro h1
      apply hv1
      have : v = h⁻¹ * v' * h := by simp only [hv']; group
      rw [this, h1]; group
    have hvv' : IsConj v v' := isConj_iff.mpr ⟨h, rfl⟩
    by_cases hv'M : v' ∈ M
    · exact ⟨v', hv'M, hv'2, hv'1, hvv'⟩
    · have hrel : M.relIndex P = 2 := by
        have h1 : M.relIndex P ≠ 1 := by
          intro h1
          exact hv'M ((Subgroup.relIndex_eq_one.mp h1) hh)
        have h0 : M.relIndex P ≠ 0 := by
          have : M.IsFiniteRelIndex P := Subgroup.isFiniteRelIndex_iff_finiteIndex.mpr inferInstance
          exact Subgroup.relIndex_ne_zero
        omega
      have hmin : ∀ y ∈ P, y ∉ M → orderOf v' ≤ orderOf y := by
        intro y _ hyM
        have hy1 : y ≠ 1 := fun h1 => hyM (h1 ▸ M.one_mem)
        have hpos := orderOf_pos y
        have hne1 : orderOf y ≠ 1 := fun h1 => hy1 (orderOf_eq_one_iff.mp h1)
        rw [hord2 v' hv'2 hv'1]
        omega
      have hcon : ∃ g : X, g⁻¹ * v' * g ∈ M := by
        by_contra hno
        push Not at hno
        obtain ⟨N, hN, hi⟩ := CFSG.ThompsonIndexTwo.exists_normal_index_two_of_thompson hP hPidx hMP hrel
          hh hv'M hmin hno
        exact not_normal_index_two_of_perfect hperf hN hi
      obtain ⟨g', hg'⟩ := hcon
      refine ⟨g'⁻¹ * v' * g', hg', ?_, ?_, ?_⟩
      · calc g'⁻¹ * v' * g' * (g'⁻¹ * v' * g') = g'⁻¹ * (v' * v') * g' := by group
          _ = 1 := by rw [hv'2]; group
      · intro h1
        apply hv'1
        have : v' = g' * (g'⁻¹ * v' * g') * g'⁻¹ := by group
        rw [this, h1]; group
      · exact hvv'.trans (isConj_iff.mpr ⟨g'⁻¹, by group⟩)
  obtain ⟨ma, hma, hma2, hma1, hca⟩ := key a ha2 ha1
  obtain ⟨mb, hmb, hmb2, hmb1, hcb⟩ := key b hb2 hb1
  have : ma = mb := eq_of_sq_eq_one_of_mem_zpowers (hMz ma hma) (hMz mb hmb) hma2 hmb2 hma1 hmb1
  rw [this] at hca
  exact hca.trans hcb.symm


theorem not_cyclic_sylow_of_perfect (hperf : commutator X = ⊤) (P : Sylow 2 X) (hP : IsCyclic P) {t : X}
    (ht1 : t ≠ 1) (htP : t ∈ (P : Subgroup X)) (ht2 : t * t = 1) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have _ : IsCyclic P := hP
  have _ : CommGroup P := IsMulCommutative.instCommGroup
  have htOrder : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact ht2) ht1
  have htwoCard : 2 ∣ Nat.card X := by
    rw [← htOrder]
    exact orderOf_dvd_natCard t
  have hminFac : (Nat.card X).minFac = 2 := (Nat.minFac_eq_two_iff (Nat.card X)).2 htwoCard
  have hnormalizer := IsCyclic.normalizer_le_centralizer hminFac hP
  let f : X →* P := MonoidHom.transferSylow P hnormalizer
  have hcomplement : f.ker.IsComplement' (P : Subgroup X) := MonoidHom.ker_transferSylow_isComplement' P hnormalizer
  have hkerTop : f.ker = ⊤ := by
    apply top_unique
    rw [← hperf]
    exact Abelianization.commutator_subset_ker (A := P) f
  have hdisjoint : Disjoint (P : Subgroup X) ⊤ := by
    have h := hcomplement.disjoint.symm
    rwa [hkerTop] at h
  have hPbot : (P : Subgroup X) = ⊥ := disjoint_top.mp hdisjoint
  apply ht1
  have : t ∈ (⊥ : Subgroup X) := by
    rw [← hPbot]
    exact htP
  simpa using this


end Perfect

section PCore

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem pPrimeCoreOf_conj_mem {H J : Subgroup G} (hJn : ∀ h ∈ H, ∀ j ∈ J, h * j * h⁻¹ ∈ J) {h : G}
    (hh : h ∈ H) {b : G} (hb : b ∈ pPrimeCoreOf 2 J) : h * b * h⁻¹ ∈ pPrimeCoreOf 2 J := by
  obtain ⟨y', hy', rfl⟩ := hb
  set φ := conjRestrict J h (hJn h hh) (fun b hb => by simpa using hJn h⁻¹ (H.inv_mem hh) b hb) with hφ
  have hchar := (pPrimeCore_characteristic (p := 2) (G := ↥J)).fixed φ
  have hmem : φ y' ∈ pPrimeCore 2 ↥J := by
    have : y' ∈ (pPrimeCore 2 ↥J).comap φ.toMonoidHom := by rw [hchar]; exact hy'
    exact this
  exact ⟨φ y', hmem, rfl⟩

theorem pPrimeCoreOf_le_of_normal {H J : Subgroup G} (hJH : J ≤ H)
    (hJn : ∀ h ∈ H, ∀ j ∈ J, h * j * h⁻¹ ∈ J) : pPrimeCoreOf 2 J ≤ pPrimeCoreOf 2 H := by
  set B := pPrimeCoreOf 2 J with hB
  have hBJ : B ≤ J := Subgroup.map_subtype_le _
  have hBH : B ≤ H := hBJ.trans hJH
  set B'' : Subgroup ↥H := B.subgroupOf H with hB''
  have hnorm : B''.Normal := ⟨fun n hn g => by
    rw [hB'', Subgroup.mem_subgroupOf] at hn ⊢
    exact pPrimeCoreOf_conj_mem hJn g.2 hn⟩
  have hcop : Nat.Coprime 2 (Nat.card B'') := by
    have h1 : Nat.card B'' = Nat.card B := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBH).toEquiv
    have h2 : Nat.card B = Nat.card (pPrimeCore 2 ↥J) :=
      Nat.card_congr (Subgroup.equivMapOfInjective _ J.subtype J.subtype_injective).symm.toEquiv
    rw [h1, h2]
    exact pPrimeCore_coprime_card
  have hle : B'' ≤ pPrimeCore 2 ↥H := le_sSup ⟨hnorm, hcop⟩
  have hmap : B''.map H.subtype = B := Subgroup.map_subgroupOf_eq_of_le hBH
  rw [← hmap]
  exact Subgroup.map_mono hle


@[expose] def centralInvolutions (J : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ J ∧ (∀ j ∈ J, x * j = j * x) ∧ x * x = 1}
  one_mem' := ⟨J.one_mem, fun j _ => by simp, by simp⟩
  mul_mem' := by
    rintro x y ⟨hxJ, hxc, hx2⟩ ⟨hyJ, hyc, hy2⟩
    refine ⟨J.mul_mem hxJ hyJ, fun j hj => ?_, ?_⟩
    · calc x * y * j = x * (y * j) := by group
        _ = x * (j * y) := by rw [hyc j hj]
        _ = (x * j) * y := by group
        _ = (j * x) * y := by rw [hxc j hj]
        _ = j * (x * y) := by group
    · have hxy : x * y = y * x := hxc y hyJ
      calc x * y * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [← hxy]
        _ = (x * x) * (y * y) := by group
        _ = 1 := by rw [hx2, hy2]; group
  inv_mem' := by
    rintro x ⟨hxJ, hxc, hx2⟩
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
    rw [hxi]
    exact ⟨hxJ, hxc, hx2⟩

omit [Finite G] in
theorem isPGroup_centralInvolutions (J : Subgroup G) : IsPGroup 2 (centralInvolutions J) := by
  intro x
  refine ⟨1, ?_⟩
  obtain ⟨_, _, hx2⟩ := x.2
  apply Subtype.ext
  show (x : G) ^ (2 ^ 1) = 1
  rw [pow_one, sq]
  exact hx2

omit [Finite G] in
theorem centralInvolutions_conj_mem {H J : Subgroup G} (hJn : ∀ h ∈ H, ∀ j ∈ J, h * j * h⁻¹ ∈ J) {h : G}
    (hh : h ∈ H) {n : G} (hn : n ∈ centralInvolutions J) : h * n * h⁻¹ ∈ centralInvolutions J := by
  obtain ⟨hnJ, hnc, hn2⟩ := hn
  refine ⟨hJn h hh n hnJ, fun j hj => ?_, ?_⟩
  · have hj' : h⁻¹ * j * h ∈ J := by simpa using hJn h⁻¹ (H.inv_mem hh) j hj
    have := hnc _ hj'
    calc h * n * h⁻¹ * j = h * (n * (h⁻¹ * j * h)) * h⁻¹ := by group
      _ = h * ((h⁻¹ * j * h) * n) * h⁻¹ := by rw [this]
      _ = j * (h * n * h⁻¹) := by group
  · calc h * n * h⁻¹ * (h * n * h⁻¹) = h * (n * n) * h⁻¹ := by group
      _ = 1 := by rw [hn2]; group

theorem no_unique_involution {H J : Subgroup G} (hJH : J ≤ H) (hJn : ∀ h ∈ H, ∀ j ∈ J, h * j * h⁻¹ ∈ J)
    (hJp : ⁅J, J⁆ = J) (hcomm : ∀ a ∈ pPrimeCoreOf 2 H, ∀ l ∈ J, a * l = l * a) {u : G} (huJ : u ∈ J)
    (hu2 : u * u = 1) (hu1 : u ≠ 1)
    (hO : ∀ N : Subgroup G, N ≤ H → (∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) → IsPGroup 2 N → u ∈ N → False)
    {P : Subgroup G} (hPJ : P ≤ J) (huP : u ∈ P) (hPp : IsPGroup 2 P) (hPidx : ¬ 2 ∣ (P.subgroupOf J).index)
    (huniq : ∀ s ∈ P, s ≠ 1 → s * s = 1 → s = u) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fintype ↥J := Fintype.ofFinite ↥J
  have hPp' : IsPGroup 2 (P.subgroupOf J) := hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPJ).symm
  let S : Sylow 2 ↥J := hPp'.toSylow hPidx
  set u' : ↥J := ⟨u, huJ⟩ with hu'
  have hperf : commutator ↥J = ⊤ := by
    have : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.mpr hJp
    exact this.commutator_eq_top
  have hu'1 : u' ≠ 1 := fun h => hu1 (congrArg Subtype.val h)
  have hu'2 : u' * u' = 1 := Subtype.ext hu2
  have hu'S : u' ∈ (S : Subgroup ↥J) := by
    show u' ∈ P.subgroupOf J
    exact huP
  have huniq' : CFSG.ZStar.UniqueInvolutionIn (S : Subgroup ↥J) u' := by
    intro s hs hs1 hs2
    have hsP : (s : G) ∈ P := hs
    exact Subtype.ext (huniq s hsP (fun h => hs1 (Subtype.ext h)) (congrArg Subtype.val hs2))
  obtain ⟨N, hNn, hNodd, hN⟩ :=
    CFSG.ZStar.BrauerSuzukiShortcut.zStarConclusion_of_perfect_uniqueInvolution_brauerSuzuki hu'1 hu'2 S hu'S
      huniq' hperf
  have hNle : N ≤ pPrimeCore 2 ↥J := le_sSup ⟨hNn, Nat.coprime_two_left.mpr hNodd⟩
  have hcomm_mem : ∀ g : ↥J, (g : G) * u * (g : G)⁻¹ * u⁻¹ ∈ pPrimeCoreOf 2 H := by
    intro g
    have h1 := hNle (hN g)
    have h2 : (g : G) * u * (g : G)⁻¹ * u⁻¹ ∈ pPrimeCoreOf 2 J := ⟨_, h1, rfl⟩
    exact pPrimeCoreOf_le_of_normal hJH hJn h2
  have hcJ : ∀ g : ↥J, (g : G) * u * (g : G)⁻¹ * u⁻¹ ∈ J := fun g =>
    J.mul_mem (J.mul_mem (J.mul_mem g.2 huJ) (J.inv_mem g.2)) (J.inv_mem huJ)
  let δ : ↥J →* ↥J :=
    { toFun := fun g => ⟨(g : G) * u * (g : G)⁻¹ * u⁻¹, hcJ g⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun g g' => by
        apply Subtype.ext
        have hc' := hcomm _ (hcomm_mem g') (g : G) g.2
        show ((g * g' : ↥J) : G) * u * ((g * g' : ↥J) : G)⁻¹ * u⁻¹ =
          ((g : G) * u * (g : G)⁻¹ * u⁻¹) * ((g' : G) * u * (g' : G)⁻¹ * u⁻¹)
        simp only [Subgroup.coe_mul]
        calc (g : G) * (g' : G) * u * ((g : G) * (g' : G))⁻¹ * u⁻¹
            = (g : G) * ((g' : G) * u * (g' : G)⁻¹ * u⁻¹) * u * (g : G)⁻¹ * u⁻¹ := by group
          _ = ((g' : G) * u * (g' : G)⁻¹ * u⁻¹) * (g : G) * u * (g : G)⁻¹ * u⁻¹ := by
            rw [hc']
          _ = _ := by
            have hcc : ((g' : G) * u * (g' : G)⁻¹ * u⁻¹) * ((g : G) * u * (g : G)⁻¹ * u⁻¹) =
                ((g : G) * u * (g : G)⁻¹ * u⁻¹) * ((g' : G) * u * (g' : G)⁻¹ * u⁻¹) := by
              have := hcomm _ (hcomm_mem g') _ (hcJ g)
              exact this.symm.symm
            rw [← hcc]; group }
  have hker : commutator ↥J ≤ δ.ker := by
    rw [commutator_def]
    refine Subgroup.commutator_le.mpr fun a _ b _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement]
    have hab : δ a * δ b = δ b * δ a := by
      apply Subtype.ext
      have := hcomm _ (hcomm_mem b) _ (hcJ a)
      exact this.symm
    rw [commutatorElement_def, hab]; group
  rw [hperf] at hker
  have hcent : ∀ g ∈ J, g * u = u * g := by
    intro g hg
    have h1 : δ ⟨g, hg⟩ = 1 := MonoidHom.mem_ker.mp (hker (Subgroup.mem_top _))
    have h2 := congrArg Subtype.val h1
    have h3 : g * u * g⁻¹ * u⁻¹ = 1 := h2
    calc g * u = (g * u * g⁻¹ * u⁻¹) * (u * g) := by group
      _ = u * g := by rw [h3, one_mul]
  exact hO (centralInvolutions J) (fun x hx => hJH hx.1) (fun h hh n hn => centralInvolutions_conj_mem hJn hh hn)
    (isPGroup_centralInvolutions J) ⟨huJ, fun j hj => (hcent j hj).symm, hu2⟩

end PCore

end CFSG.GH74.GLS.Stage2.Final.Thm6.L20
