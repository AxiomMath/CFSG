module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.DeltaTransitivity

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.DeltaSemiregularity

open CFSG.LocalAnalysis.RankThreeUC.Section5

open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem conj_of_odd {K : Type} [Group K] [Finite K] (N : Subgroup K) [N.Normal]
    (hN : IsPGroup 2 N) (x y : K) (hx : Odd (orderOf x)) (hord : orderOf y = orderOf x)
    (hxy : x * y⁻¹ ∈ N) (htop : ∀ k : K, ∃ n ∈ N, ∃ j : ℤ, k = n * x ^ j) :
    ∃ m ∈ N, y = m * x * m⁻¹ := by
  classical
  have hdisj : ∀ z : K, Odd (orderOf z) → ∀ g ∈ N, g ∈ Subgroup.zpowers z → g = 1 := by
    intro z hz g hgN hgz
    have h1 : orderOf g ∣ orderOf z := by
      have := Subgroup.orderOf_dvd_natCard _ hgz
      rwa [Nat.card_zpowers] at this
    obtain ⟨k, hk⟩ := hN.exists_card_eq
    have h2 : orderOf g ∣ 2 ^ k := by
      rw [← hk]; exact Subgroup.orderOf_dvd_natCard N hgN
    have h3 : orderOf g ∣ 1 := by
      have : Nat.Coprime (orderOf z) (2 ^ k) := Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hz)
      exact this ▸ Nat.dvd_gcd h1 h2
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)
  have hy : Odd (orderOf y) := hord ▸ hx
  have hxN : N ⊓ Subgroup.zpowers x = ⊥ := by
    rw [eq_bot_iff]; rintro g ⟨h1, h2⟩; exact hdisj x hx g h1 h2
  have hyN : N ⊓ Subgroup.zpowers y = ⊥ := by
    rw [eq_bot_iff]; rintro g ⟨h1, h2⟩; exact hdisj y hy g h1 h2
  have hNx : (N : Set K) * (Subgroup.zpowers x : Set K) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro k
    obtain ⟨n, hn, j, rfl⟩ := htop k
    exact Set.mem_mul.2 ⟨n, hn, x ^ j, Subgroup.zpow_mem_zpowers x j, rfl⟩
  have hNy : (N : Set K) * (Subgroup.zpowers y : Set K) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro k
    obtain ⟨n, hn, j, rfl⟩ := htop k
    have hq : (QuotientGroup.mk x : K ⧸ N) = QuotientGroup.mk y := by
      have := (QuotientGroup.eq_one_iff (N := N) (x * y⁻¹)).2 hxy
      rwa [QuotientGroup.mk_mul, QuotientGroup.mk_inv, mul_inv_eq_one] at this
    have hqj : (QuotientGroup.mk (x ^ j) : K ⧸ N) = QuotientGroup.mk (y ^ j) := by
      rw [QuotientGroup.mk_zpow, QuotientGroup.mk_zpow, hq]
    have hm : x ^ j * (y ^ j)⁻¹ ∈ N := by
      rw [← QuotientGroup.eq_one_iff (N := N), QuotientGroup.mk_mul, QuotientGroup.mk_inv, hqj, mul_inv_cancel]
    refine Set.mem_mul.2 ⟨n * (x ^ j * (y ^ j)⁻¹), N.mul_mem hn hm, y ^ j, Subgroup.zpow_mem_zpowers y j, ?_⟩
    group
  haveI : Group.IsSolvable N := by
    haveI : Group.IsNilpotent N := hN.isNilpotent
    infer_instance
  have hcop : Nat.Coprime (Nat.card N) N.index := by
    have hc := Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hxN) hNx
    rw [hc.symm.index_eq_card, Nat.card_zpowers]
    obtain ⟨k, hk⟩ := hN.exists_card_eq
    rw [hk]; exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hx)
  obtain ⟨n, hn, hxe⟩ := CFSG.SolvableHall.solvable_normal_hall_complement_conjugacy N inferInstance hcop hNx hNy hxN hyN
  obtain ⟨j, hj⟩ : ∃ j : ℤ, y = n⁻¹ * x ^ j * n := by
    have : y ∈ (Subgroup.zpowers x).map (MulAut.conj n⁻¹).toMonoidHom := hxe ▸ Subgroup.mem_zpowers y
    obtain ⟨g, hg, hgy⟩ := this
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    exact ⟨j, by rw [← hgy]; simp [MulAut.conj_apply]⟩
  have hq : (QuotientGroup.mk x : K ⧸ N) = QuotientGroup.mk y := by
    have := (QuotientGroup.eq_one_iff (N := N) (x * y⁻¹)).2 hxy
    rwa [QuotientGroup.mk_mul, QuotientGroup.mk_inv, mul_inv_eq_one] at this
  have hq2 : (QuotientGroup.mk y : K ⧸ N) = QuotientGroup.mk (x ^ j) := by
    rw [hj, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have : (QuotientGroup.mk n : K ⧸ N) = 1 := (QuotientGroup.eq_one_iff n).2 hn
    rw [this]; simp
  have h3 : x⁻¹ * x ^ j ∈ N := (QuotientGroup.eq (s := N)).1 (hq.trans hq2)
  have h4 : x⁻¹ * x ^ j ∈ Subgroup.zpowers x :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers x)) (Subgroup.zpow_mem_zpowers x j)
  have h5 := hdisj x hx _ h3 h4
  have h6 : x ^ j = x := by simpa [inv_mul_eq_one, eq_comm] using h5
  refine ⟨n⁻¹, N.inv_mem hn, ?_⟩
  rw [hj, h6]; simp

private theorem comm_stable {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : BinaryActionRankCounterexample G p P T B e ρ) {b : G} (hb : b ∈ B) (hb1 : b ≠ 1) :
    ∀ w : G, w * b * w⁻¹ = b → ∀ z ∈ ⁅B, P⁆, w⁻¹ * z * w ∈ ⁅B, P⁆ := by
  classical
  have hS := hc.oddPrimeClassTwoAction.setting
  have hP : P.Normal := hc.faithfulBinaryIrreducibleAction.normal
  have hel := isElemAbelian_of_binary_rank_counterexample hc
  have hcomm : ∀ a ∈ P, ∀ c ∈ P, a * c = c * a := fun a ha c hc' =>
    congrArg Subtype.val (hel.1.is_comm.comm ⟨a, ha⟩ ⟨c, hc'⟩)
  have hexp : ∀ x ∈ P, x ^ p = 1 := fun x hx => by
    have := Monoid.pow_exponent_eq_one (⟨x, hx⟩ : P)
    rw [hS.exponent] at this
    exact congrArg Subtype.val this
  have hBP : B ≤ Subgroup.normalizer (P : Set G) := hS.normB
  obtain ⟨hDmem, -, -⟩ := CanonicalBFixedHyperplane.canonical hc
  have hnP : ∀ x ∈ P, b * x * b⁻¹ ∈ P := fun x hx =>
    (Subgroup.mem_normalizer_iff.1 (hBP hb) x).1 hx
  have hCb : Nat.card ↥(P ⊓ Subgroup.centralizer ({b} : Set G)) ≤ p := by
    obtain ⟨g, hg⟩ := (hc.oddPrimeClassTwoAction.cyclic_centralizer b hb hb1).exists_generator
    rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
    refine Nat.le_of_dvd hS.prime.pos (orderOf_dvd_of_pow_eq_one ?_)
    apply Subtype.ext
    exact hexp g.1 (Subgroup.mem_inf.1 g.2).1
  let φ : P →* P := MonoidHom.mk' (fun x => ⟨b * x * b⁻¹ * (x : G)⁻¹,
      P.mul_mem (hnP x x.2) (P.inv_mem x.2)⟩) (by
    intro x y
    apply Subtype.ext
    have hA : b * (y : G) * b⁻¹ * (y : G)⁻¹ ∈ P := P.mul_mem (hnP y y.2) (P.inv_mem y.2)
    have := hcomm _ hA _ (P.inv_mem x.2)
    show b * ((x : G) * y) * b⁻¹ * ((x : G) * y)⁻¹ =
      (b * (x : G) * b⁻¹ * (x : G)⁻¹) * (b * (y : G) * b⁻¹ * (y : G)⁻¹)
    calc b * ((x : G) * y) * b⁻¹ * ((x : G) * y)⁻¹
        = (b * (x : G) * b⁻¹) * (b * (y : G) * b⁻¹ * (y : G)⁻¹) * (x : G)⁻¹ := by group
      _ = (b * (x : G) * b⁻¹) * ((x : G)⁻¹ * (b * (y : G) * b⁻¹ * (y : G)⁻¹)) := by
          rw [mul_assoc _ _ ((x : G)⁻¹), this]
      _ = _ := by group)
  have hφ : ∀ x : P, (φ x : G) = b * x * b⁻¹ * (x : G)⁻¹ := fun x => rfl
  have hker : φ.ker.map P.subtype ≤ P ⊓ Subgroup.centralizer ({b} : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨x.2, ?_⟩
    have h1 : b * (x : G) * b⁻¹ * (x : G)⁻¹ = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
      rwa [hφ] at this
    show (x : G) ∈ Subgroup.centralizer ({b} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    show h * (x : G) = (x : G) * h
    have h2 : h * (x : G) * h⁻¹ = x := by
      have := mul_inv_eq_one.1 h1
      exact this
    calc h * (x : G) = (h * x * h⁻¹) * h := by group
      _ = _ := by rw [h2]
  have hkerc : Nat.card φ.ker ≤ p := by
    have h1 := Subgroup.card_le_of_le hker
    rw [Subgroup.card_map_of_injective P.subtype_injective] at h1
    exact h1.trans hCb
  have hrange : φ.range ≤ (⁅B, P⁆).subgroupOf P := by
    rintro _ ⟨x, rfl⟩
    show (φ x : G) ∈ ⁅B, P⁆
    rw [hφ]
    exact Subgroup.commutator_mem_commutator hb x.2
  have hDcard : Nat.card ((⁅B, P⁆).subgroupOf P) * p = Nat.card P := by
    have := Subgroup.card_mul_index ((⁅B, P⁆).subgroupOf P)
    rw [← this]
    congr 1
    exact hDmem.2.1.symm
  have hRcard : Nat.card φ.range * Nat.card φ.ker = Nat.card P := by
    rw [← Subgroup.index_ker, mul_comm]; exact Subgroup.card_mul_index φ.ker
  have hge : Nat.card ((⁅B, P⁆).subgroupOf P) ≤ Nat.card φ.range := by
    have h1 : Nat.card ((⁅B, P⁆).subgroupOf P) * p ≤ Nat.card φ.range * p := by
      rw [hDcard, ← hRcard]
      exact Nat.mul_le_mul_left _ hkerc
    exact Nat.le_of_mul_le_mul_right h1 hS.prime.pos
  have hRD : φ.range = (⁅B, P⁆).subgroupOf P := Subgroup.eq_of_le_of_card_ge hrange hge
  have himg : ∀ z ∈ ⁅B, P⁆, ∃ x ∈ P, z = b * x * b⁻¹ * x⁻¹ := by
    intro z hz
    have hzP : z ∈ P := hDmem.1 hz
    have : (⟨z, hzP⟩ : P) ∈ φ.range := by
      rw [hRD]; exact hz
    obtain ⟨x, hx⟩ := this
    have h2 := congrArg Subtype.val hx
    rw [hφ] at h2
    exact ⟨x, x.2, h2.symm⟩
  intro w hw z hz
  have hw' : w⁻¹ * b * w = b := by
    have h1 : w * b = b * w := by
      have := congrArg (· * w) hw
      simpa [mul_assoc] using this
    calc w⁻¹ * b * w = w⁻¹ * (b * w) := by group
      _ = w⁻¹ * (w * b) := by rw [h1]
      _ = b := by group
  obtain ⟨x, hxP, rfl⟩ := himg z hz
  have h1 : w⁻¹ * (b * x * b⁻¹ * x⁻¹) * w = b * (w⁻¹ * x * w) * b⁻¹ * (w⁻¹ * x * w)⁻¹ := by
    calc w⁻¹ * (b * x * b⁻¹ * x⁻¹) * w
        = (w⁻¹ * b * w) * (w⁻¹ * x * w) * (w⁻¹ * b * w)⁻¹ * (w⁻¹ * x * w)⁻¹ := by group
      _ = _ := by rw [hw']
  rw [h1]
  exact Subgroup.commutator_mem_commutator hb (by
    have := hP.conj_mem x hxP w⁻¹
    simpa using this)

theorem semiregular {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : BinaryActionRankCounterexample G p P T B e ρ) :
    ∀ b ∈ B, b ≠ 1 → ∀ F ∈ Delta p P ρ, F ≠ ⁅B, P⁆ →
      b ∉ Subgroup.normalizer (F : Set G) := by
  classical
  intro b hb hb1 F hF hFD hbF
  have hS := hc.oddPrimeClassTwoAction.setting
  have hP : P.Normal := hc.faithfulBinaryIrreducibleAction.normal
  obtain ⟨hDmem, -, huniq⟩ := CanonicalBFixedHyperplane.canonical hc
  have hBD : B ≤ Subgroup.normalizer ((⁅B, P⁆ : Subgroup G) : Set G) := by
    obtain ⟨s, -, hs⟩ := OrbitHasBFixedMember.exists_member hc hDmem
    have hmem := DeltaConjugationAction.map_mem (p := p) hP ρ s hDmem
    have heq := huniq _ hmem (fun b hb => hs b hb)
    intro c hc'
    have := hs c hc'
    rwa [heq] at this
  obtain ⟨n, hn, hFn⟩ := DeltaTransitivity.transitive hc _ hDmem F hF
  have hstab := comm_stable hc hb hb1
  set D : Subgroup G := ⁅B, P⁆ with hDdef
  have hmemF : ∀ x, x ∈ F ↔ n⁻¹ * x * n ∈ D := by
    intro x; rw [hFn, Subgroup.mem_map_equiv]; simp [MulAut.conj_symm_apply]
  have hbF' := Subgroup.mem_normalizer_iff.1 hbF
  have hb'N : n⁻¹ * b * n ∈ Subgroup.normalizer (D : Set G) := by
    rw [Subgroup.mem_normalizer_iff]; intro h
    calc h ∈ D ↔ n * h * n⁻¹ ∈ F := by rw [hmemF]; simp [mul_assoc]
      _ ↔ b * (n * h * n⁻¹) * b⁻¹ ∈ F := hbF' _
      _ ↔ n⁻¹ * (b * (n * h * n⁻¹) * b⁻¹) * n ∈ D := hmemF _
      _ ↔ (n⁻¹ * b * n) * h * (n⁻¹ * b * n)⁻¹ ∈ D := by
          rw [show n⁻¹ * (b * (n * h * n⁻¹) * b⁻¹) * n =
            (n⁻¹ * b * n) * h * (n⁻¹ * b * n)⁻¹ by group]
  set S : Subgroup G := twoCoreCommutator T B with hSdef
  have hS2 : IsPGroup 2 S := by
    have hK : IsPGroup 2 (CFSG.Open.pCoreOf 2 (B ⊔ T)) :=
      (CFSG.LieType.BorelTits.pCore_isPGroup 2).map (B ⊔ T).subtype
    exact hK.to_le (SstarQuotientFaithful.Xs_le_pCoreOf T B le_sup_left)
  have hBnorm : B ≤ Subgroup.normalizer (S : Set G) := by
    apply Subgroup.le_normalizer_iff_commutator_le_left.mpr
    exact (CoprimeStarSubgroupStructure.Xs_generated hc.oddPrimeClassTwoAction).le
  have hbS : ∀ s ∈ S, b * s * b⁻¹ ∈ S := fun s hs =>
    (Subgroup.mem_normalizer_iff.1 (hBnorm hb) s).1 hs
  have hbzp : Subgroup.zpowers b ≤ Subgroup.normalizer (S : Set G) := by
    rw [Subgroup.zpowers_le]; exact hBnorm hb
  have hbD : b ∈ Subgroup.normalizer (D : Set G) := hBD hb
  set Kg : Subgroup G := Subgroup.normalizer (D : Set G) ⊓ (S ⊔ Subgroup.zpowers b) with hKg
  set M0 : Subgroup G := S ⊓ Subgroup.normalizer (D : Set G) with hM0
  let N : Subgroup Kg := M0.subgroupOf Kg
  have hKS : S ⊔ Subgroup.zpowers b ≤ Subgroup.normalizer (S : Set G) :=
    sup_le Subgroup.le_normalizer hbzp
  haveI hNN : N.Normal := ⟨fun k hk g => by
    have hk' : (k : G) ∈ M0 := hk
    show ((g * k * g⁻¹ : Kg) : G) ∈ M0
    refine ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.1 (hKS g.2.2) k).1 hk'.1
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ g.2.1 hk'.2) (Subgroup.inv_mem _ g.2.1)⟩
  have hN2 : IsPGroup 2 N := (hS2.to_le (inf_le_left : M0 ≤ S)).comap_subtype
  have hbK : b ∈ Kg := ⟨hbD, Subgroup.mem_sup_right (Subgroup.mem_zpowers b)⟩
  have hb'K : n⁻¹ * b * n ∈ Kg := by
    refine ⟨hb'N, ?_⟩
    have : n⁻¹ * b * n = (n⁻¹ * (b * n * b⁻¹)) * b := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (S.mul_mem (S.inv_mem hn) (hbS n hn)))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers b))
  let x : Kg := ⟨b, hbK⟩
  let y : Kg := ⟨n⁻¹ * b * n, hb'K⟩
  have hbodd : Odd (orderOf b) :=
    Odd.of_dvd_nat hS.oddOrder (Subgroup.orderOf_dvd_natCard B hb)
  have hx : Odd (orderOf x) := by
    rw [← Subgroup.orderOf_coe]; exact hbodd
  have hord : orderOf y = orderOf x := by
    rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
    show orderOf (n⁻¹ * b * n) = orderOf b
    simpa [MulAut.conj_apply] using
      orderOf_injective (MulAut.conj n⁻¹).toMonoidHom (MulAut.conj n⁻¹).injective b
  have hxy : x * y⁻¹ ∈ N := by
    show ((x * y⁻¹ : Kg) : G) ∈ M0
    have : ((x * y⁻¹ : Kg) : G) = (b * n⁻¹ * b⁻¹) * n := by
      show b * (n⁻¹ * b * n)⁻¹ = _
      group
    rw [this]
    refine ⟨S.mul_mem (hbS _ (S.inv_mem hn)) hn, ?_⟩
    rw [← this]
    exact Subgroup.mul_mem _ hbD (Subgroup.inv_mem _ hb'N)
  have htop : ∀ k : Kg, ∃ nn ∈ N, ∃ j : ℤ, k = nn * x ^ j := by
    intro k
    have hk2 : (k : G) ∈ ((S ⊔ Subgroup.zpowers b : Subgroup G) : Set G) := k.2.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left S _ hbzp] at hk2
    obtain ⟨s, hs, z, hz, hsz⟩ := Set.mem_mul.1 hk2
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    have hsND : s ∈ Subgroup.normalizer (D : Set G) := by
      have : s = (k : G) * (b ^ j)⁻¹ := by rw [← hsz]; group
      rw [this]
      exact Subgroup.mul_mem _ k.2.1 (Subgroup.inv_mem _ (Subgroup.zpow_mem _ hbD j))
    refine ⟨⟨s, ⟨hsND, Subgroup.mem_sup_left hs⟩⟩, ⟨hs, hsND⟩, j, ?_⟩
    apply Subtype.ext
    show (k : G) = s * b ^ j
    exact hsz.symm
  obtain ⟨m, hm, hmy⟩ := conj_of_odd N hN2 x y hx hord hxy htop
  have hm1 : (m : G) ∈ S := (hm : (m : G) ∈ M0).1
  have hm2 : (m : G) ∈ Subgroup.normalizer (D : Set G) := (hm : (m : G) ∈ M0).2
  have hmy' : n⁻¹ * b * n = (m : G) * b * (m : G)⁻¹ := congrArg Subtype.val hmy
  have hcommute : (n * (m : G)) * b * (n * (m : G))⁻¹ = b := by
    calc (n * (m : G)) * b * (n * (m : G))⁻¹ = n * ((m : G) * b * (m : G)⁻¹) * n⁻¹ := by group
      _ = n * (n⁻¹ * b * n) * n⁻¹ := by rw [hmy']
      _ = b := by group
  have hcommute' : (n * (m : G))⁻¹ * b * (n * (m : G))⁻¹⁻¹ = b := by
    have h1 : (n * (m : G)) * b = b * (n * (m : G)) := by
      have := congrArg (· * (n * (m : G))) hcommute
      simpa [mul_assoc] using this
    calc (n * (m : G))⁻¹ * b * (n * (m : G))⁻¹⁻¹ = (n * (m : G))⁻¹ * (b * (n * (m : G))) := by group
      _ = (n * (m : G))⁻¹ * ((n * (m : G)) * b) := by rw [h1]
      _ = b := by group
  apply hFD
  ext z
  rw [hmemF]
  have hmD := Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hm2) (n⁻¹ * z * n)
  rw [inv_inv] at hmD
  rw [hmD]
  have hrw : (m : G)⁻¹ * (n⁻¹ * z * n) * (m : G) = (n * (m : G))⁻¹ * z * (n * (m : G)) := by group
  rw [hrw]
  constructor
  · intro h
    have := hstab _ hcommute' _ h
    simpa [mul_assoc] using this
  · intro h
    exact hstab _ hcommute _ h

end CFSG.LocalAnalysis.RankThreeUC.Section5.DeltaSemiregularity
end
