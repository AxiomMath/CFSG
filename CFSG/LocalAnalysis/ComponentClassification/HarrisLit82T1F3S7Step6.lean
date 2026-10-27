module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S73U2
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1C3Step9
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3S7Step4

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank CFSG.ComponentClassification.UnbalancedLayer
open CFSG.LieType.Universal.Spin CliffordAlgebra CFSG.ABGLocalTools
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem F3S7.oPrimeResidual_normal (X : Type*) [Group X] :
    (GH74.GLS.oPrimeResidual 2 X).Normal := by
  refine ⟨fun n hn g => ?_⟩
  unfold GH74.GLS.oPrimeResidual at hn ⊢
  induction hn using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, hk⟩ := hx
    refine Subgroup.subset_closure ⟨k, ?_⟩
    calc (g * x * g⁻¹) ^ (2 ^ k) = g * x ^ (2 ^ k) * g⁻¹ := by rw [conj_pow]
      _ = 1 := by rw [hk]; group
  | one => simp
  | mul a b _ _ ha hb =>
    have h1 : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [h1]
    exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    have h1 : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [h1]
    exact Subgroup.inv_mem _ ha

theorem F3S7.map_pPrimeCore_of_subnormal {D M : Subgroup G} (hDM : D ≤ M)
    (hD : (D.subgroupOf M).IsSubnormal) :
    (pPrimeCore 2 ↥D).map D.subtype = D ⊓ (pPrimeCore 2 ↥M).map M.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key := CFSG.LocalCores.prime_set_core_subnormal_intersection
    {q : Nat.Primes | q.val ≠ 2} hD
  rw [← pPrimeCore_eq_piCore, ← pPrimeCore_eq_piCore] at key
  have h1 := congrArg (Subgroup.map M.subtype) key
  rwa [F3S7.map_pPrimeCore_subgroupOf hDM, Subgroup.map_inf_eq _ _ _ M.subtype_injective,
    subgroupOf_map_subtype, inf_eq_left.mpr hDM] at h1

omit [Finite G] in
theorem F3S7.isSolvableTwoComponentIn_of_subgroupOf {J A M : Subgroup G} (hJA : J ≤ A)
    (hAM : A ≤ M) (h : IsSolvableTwoComponentIn (J.subgroupOf M) (A.subgroupOf M)) :
    IsSolvableTwoComponentIn J A := by
  have hJM : J ≤ M := hJA.trans hAM
  let eA : ↥(A.subgroupOf M) ≃* ↥A := subgroupOfEquivOfLe hAM
  let eJ : ↥(J.subgroupOf M) ≃* ↥J := subgroupOfEquivOfLe hJM
  refine ⟨hJA, ?_, ?_, ?_⟩
  · have hmap : ((J.subgroupOf M).subgroupOf (A.subgroupOf M)).map eA.toMonoidHom =
        J.subgroupOf A := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨eA.symm x, hx, eA.apply_symm_apply x⟩
    rw [← hmap]
    exact h.2.1.map eA.surjective
  · have h1 := congrArg (Subgroup.map M.subtype) h.2.2.1
    rw [map_map, map_map] at h1
    have h2 : M.subtype.comp (J.subgroupOf M).subtype = J.subtype.comp eJ.toMonoidHom :=
      MonoidHom.ext fun _ => rfl
    have h3 : M.subtype.comp (A.subgroupOf M).subtype = A.subtype.comp eA.toMonoidHom :=
      MonoidHom.ext fun _ => rfl
    rwa [h2, h3, ← map_map, ← map_map, pPrimeCore_map_iso 2 eJ, pPrimeCore_map_iso 2 eA] at h1
  · rcases h.2.2.2 with h1 | h1
    · obtain ⟨e⟩ := h1
      exact .inl ⟨(QuotientGroup.congr _ _ eJ.symm (pPrimeCore_map_iso 2 eJ.symm)).trans e⟩
    · obtain ⟨e⟩ := h1
      exact .inr ⟨(QuotientGroup.congr _ _ eJ.symm (pPrimeCore_map_iso 2 eJ.symm)).trans e⟩

theorem F3S7.isSolvableTwoComponentIn_map_bar {X : Type} [Group X] [Finite X] {t : X}
    (ht : orderOf t = 2)
    (hO : pPrimeCore 2 ↥(centralizer {(QuotientGroup.mk t : X ⧸ pPrimeCore 2 X)}) = ⊥)
    {J : Subgroup X} (hJ : IsSolvableTwoComponentIn J (centralizer {t})) :
    IsSolvableTwoComponentIn (J.map (QuotientGroup.mk' (pPrimeCore 2 X)))
      (centralizer {(QuotientGroup.mk t : X ⧸ pPrimeCore 2 X)}) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 X) with hπ
  set C := centralizer ({t} : Set X) with hC
  set C' := centralizer ({(QuotientGroup.mk t : X ⧸ pPrimeCore 2 X)} :
    Set (X ⧸ pPrimeCore 2 X)) with hC'
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hCmap : C.map π = C' := map_centralizer_eq (odd_card_pPrimeCore_two X) htt
  let φ : ↥C →* ↥C' := (π.comp C.subtype).codRestrict _ (fun x => hCmap ▸ mem_map_of_mem π x.2)
  have hφs : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    rw [← hCmap] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hOC : ∀ c ∈ pPrimeCore 2 ↥C, π (c : X) = 1 := by
    intro c hc
    have hN : ((pPrimeCore 2 ↥C).map φ).Normal :=
      (pPrimeCore_normal (p := 2) (G := ↥C)).map φ hφs
    have hNodd : Odd (Nat.card ↥((pPrimeCore 2 ↥C).map φ)) :=
      (odd_card_pPrimeCore_two ↥C).of_dvd_nat (Subgroup.card_map_dvd _ _)
    have hle : (pPrimeCore 2 ↥C).map φ ≤ pPrimeCore 2 ↥C' :=
      le_sSup (s := {K : Subgroup ↥C' | K.Normal ∧ Nat.Coprime 2 (Nat.card K)})
        ⟨hN, Nat.coprime_two_left.mpr hNodd⟩
    have h1 := hle (mem_map_of_mem φ hc)
    rw [hO, mem_bot] at h1
    exact congrArg Subtype.val h1
  set Jb := J.map π with hJb
  let ψ : ↥J →* ↥Jb := (π.comp J.subtype).codRestrict _ (fun x => mem_map_of_mem π x.2)
  have hψs : Function.Surjective ψ := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hker : ψ.ker = pPrimeCore 2 ↥J := by
    apply le_antisymm
    · have hkodd : Nat.Coprime 2 (Nat.card ψ.ker) := by
        refine Nat.coprime_two_left.mpr ((odd_card_pPrimeCore_two X).of_dvd_nat ?_)
        have hle : ψ.ker.map J.subtype ≤ pPrimeCore 2 X := by
          rintro _ ⟨x, hx, rfl⟩
          have hx' : π (x : X) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
          rwa [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at hx'
        rw [← Subgroup.card_map_of_injective J.subtype_injective]
        exact Subgroup.card_dvd_of_le hle
      exact le_sSup (s := {K : Subgroup ↥J | K.Normal ∧ Nat.Coprime 2 (Nat.card K)})
        ⟨MonoidHom.normal_ker ψ, hkodd⟩
    · intro x hx
      have hx' : (x : X) ∈ (pPrimeCore 2 ↥C).map C.subtype := by
        rw [← hJ.2.2.1]
        exact mem_map_of_mem _ hx
      obtain ⟨c, hc, hcx⟩ := hx'
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      change π (x : X) = 1
      rw [← hcx]
      exact hOC c hc
  have hkodd : ¬ 2 ∣ Nat.card ψ.ker := by
    rw [hker]
    exact fun h2 => (Nat.not_even_iff_odd.mpr (odd_card_pPrimeCore_two ↥J))
      (even_iff_two_dvd.mpr h2)
  obtain ⟨e₀⟩ := GSThmB.OddQuot.nonempty_pPrimeCore_equiv_of_surjective ψ hψs hkodd
  let e₁ : ↥J ⧸ pPrimeCore 2 ↥J ≃* ↥Jb :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)
  have hOb : pPrimeCore 2 ↥Jb = ⊥ := by
    have hc1 := Nat.card_congr e₁.toEquiv
    have hc2 := Nat.card_congr e₀.toEquiv
    have hc3 := Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥Jb)
    have hpos : 0 < Nat.card ↥Jb := Nat.card_pos
    apply Subgroup.eq_bot_of_card_eq
    have h4 : Nat.card ↥Jb * Nat.card ↥(pPrimeCore 2 ↥Jb) = Nat.card ↥Jb * 1 := by
      rw [mul_one]
      conv_rhs => rw [hc3]
      rw [← hc2, hc1]
    exact Nat.eq_of_mul_eq_mul_left hpos h4
  refine ⟨(map_mono hJ.1).trans hCmap.le, ?_, ?_, ?_⟩
  · have hmap : (J.subgroupOf C).map φ = Jb.subgroupOf C' := by
      ext ⟨y, hy⟩
      constructor
      · rintro ⟨x, hx, hxy⟩
        exact ⟨x, hx, congrArg Subtype.val hxy⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hJ.1 hx⟩, hx, rfl⟩
    rw [← hmap]
    exact hJ.2.1.map hφs
  · rw [hOb, hO, Subgroup.map_bot, Subgroup.map_bot]
  · rcases hJ.2.2.2 with h1 | h1
    · obtain ⟨ε⟩ := h1
      exact .inl ⟨e₀.symm.trans ε⟩
    · obtain ⟨ε⟩ := h1
      exact .inr ⟨e₀.symm.trans ε⟩

theorem F3S7.mem_of_two_pow_of_sup {L K : Subgroup G} (hKN : K ≤ normalizer (L : Set G))
    (hKL : GH74.GLS.oPrimeResidualOf 2 K ≤ L) {x : G} (hx : x ∈ L ⊔ K) {n : ℕ}
    (hxn : x ^ 2 ^ n = 1) : x ∈ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := GH74.GLS.oPrimeResidual 2 ↥K with hR
  have hRn : R.Normal := F3S7.oPrimeResidual_normal ↥K
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥K) := inferInstance
  have hPR : (P : Subgroup ↥K) ≤ R := by
    intro s hs
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨s, hs⟩
    exact Subgroup.subset_closure ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hodd : Odd R.index := by
    have h1 : R.index ∣ (P : Subgroup ↥K).index := Subgroup.index_dvd_of_le hPR
    have h2 : ¬ 2 ∣ (P : Subgroup ↥K).index := P.not_dvd_index
    exact Odd.of_dvd_nat (Nat.odd_iff.2 (by omega)) h1
  have hkm : ∀ k ∈ K, k ^ R.index ∈ L := by
    intro k hk
    have h1 : (QuotientGroup.mk (⟨k, hk⟩ : ↥K) : ↥K ⧸ R) ^ R.index = 1 := by
      rw [Subgroup.index_eq_card]
      exact pow_card_eq_one'
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h1
    have h2 := hKL ⟨_, h1, rfl⟩
    simpa using h2
  have hxs : x ∈ ((L ⊔ K : Subgroup G) : Set G) := hx
  rw [coe_mul_of_right_le_normalizer_left L K hKN] at hxs
  obtain ⟨l, hl, k, hk, rfl⟩ := hxs
  have hpow : ∀ j : ℕ, (l * k) ^ j * (k ^ j)⁻¹ ∈ L := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hc : k ^ j * l * (k ^ j)⁻¹ ∈ L :=
        (mem_normalizer_iff.mp (hKN (pow_mem hk j)) l).mp hl
      have h3 : (l * k) ^ (j + 1) * (k ^ (j + 1))⁻¹ =
          ((l * k) ^ j * (k ^ j)⁻¹) * (k ^ j * l * (k ^ j)⁻¹) := by
        rw [pow_succ, pow_succ]
        group
      rw [h3]
      exact mul_mem ih hc
  have hxm : (l * k) ^ R.index ∈ L := by
    have h1 := mul_mem (hpow R.index) (hkm k hk)
    rwa [inv_mul_cancel_right] at h1
  have hcop : Nat.Coprime R.index (orderOf (l * k)) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hxn)
      ((Nat.coprime_two_right.mpr hodd).pow_right n)
  obtain ⟨a, ha⟩ := exists_pow_eq_self_of_coprime hcop
  show l * k ∈ L
  rw [← ha]
  exact pow_mem hxm a

theorem F3S7.oPrimeResidualOf_sup_eq {L K : Subgroup G} (hKN : K ≤ normalizer (L : Set G))
    (hKL : GH74.GLS.oPrimeResidualOf 2 K ≤ L) (hL : Group.IsPerfect ↥L) :
    GH74.GLS.oPrimeResidualOf 2 (L ⊔ K) = L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := L ⊔ K with hXdef
  have hLX : L ≤ X := le_sup_left
  apply le_antisymm
  · unfold GH74.GLS.oPrimeResidualOf GH74.GLS.oPrimeResidual
    rw [MonoidHom.map_closure, closure_le]
    rintro _ ⟨x, ⟨k, hk⟩, rfl⟩
    exact F3S7.mem_of_two_pow_of_sup hKN hKL x.2 (n := k)
      (by simpa using congrArg Subtype.val hk)
  · have hRn : (GH74.GLS.oPrimeResidual 2 ↥X).Normal := F3S7.oPrimeResidual_normal ↥X
    set R : Subgroup ↥(L.subgroupOf X) :=
      (GH74.GLS.oPrimeResidual 2 ↥X).subgroupOf (L.subgroupOf X) with hR
    have hPperf' : Group.IsPerfect ↥(L.subgroupOf X) :=
      Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hLX).symm.toMonoidHom)
        (subgroupOfEquivOfLe hLX).symm.surjective
    have hRn' : R.Normal := Subgroup.Normal.subgroupOf hRn _
    obtain ⟨S⟩ : Nonempty (Sylow 2 ↥(L.subgroupOf X)) := inferInstance
    have hSR : (S : Subgroup ↥(L.subgroupOf X)) ≤ R := by
      intro x hx
      obtain ⟨k, hk⟩ := S.isPGroup' ⟨x, hx⟩
      refine Subgroup.subset_closure ⟨k, ?_⟩
      have := congrArg (fun w : ↥S => (((w : ↥(L.subgroupOf X)) : ↥X))) hk
      simpa using this
    have hodd : Odd R.index := by
      have h1 : R.index ∣ (S : Subgroup ↥(L.subgroupOf X)).index :=
        Subgroup.index_dvd_of_le hSR
      have h2 : ¬ 2 ∣ (S : Subgroup ↥(L.subgroupOf X)).index := S.not_dvd_index
      exact Odd.of_dvd_nat (Nat.odd_iff.2 (by omega)) h1
    have : Group.IsPerfect (↥(L.subgroupOf X) ⧸ R) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective R)
    have : Group.IsSolvable (↥(L.subgroupOf X) ⧸ R) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    have hsub : Subsingleton (↥(L.subgroupOf X) ⧸ R) := by
      by_contra hns
      have : Nontrivial (↥(L.subgroupOf X) ⧸ R) := not_subsingleton_iff_nontrivial.1 hns
      have h1 := Group.IsSolvable.commutator_lt_top_of_nontrivial (↥(L.subgroupOf X) ⧸ R)
      rw [Group.IsPerfect.commutator_eq_top] at h1
      exact lt_irrefl _ h1
    have hRtop : R = ⊤ := by
      rw [← Subgroup.index_eq_one]
      have : Nat.card (↥(L.subgroupOf X) ⧸ R) = 1 := Nat.card_unique
      exact this
    intro l hl
    have hlX : l ∈ X := hLX hl
    have hlR : (⟨⟨l, hlX⟩, Subgroup.mem_subgroupOf.2 hl⟩ : ↥(L.subgroupOf X)) ∈ R :=
      hRtop ▸ Subgroup.mem_top _
    exact ⟨⟨l, hlX⟩, hlR, rfl⟩

theorem F3S7.exists_lift_solvable {z u : G} {L : Subgroup G}
    (hL : IsTwoComponentIn L (centralizer {z})) (huL : u ∈ L) (hu : orderOf u = 2)
    {Y : Subgroup (↥L ⧸ pPrimeCore 2 ↥L)}
    (hY : IsSolvableTwoComponentIn Y
      (centralizer {(QuotientGroup.mk ⟨u, huL⟩ : ↥L ⧸ pPrimeCore 2 ↥L)}))
    (eY : ↥Y ⧸ pPrimeCore 2 ↥Y ≃* SL(2, ZMod 3)) :
    ∃ J : Subgroup G, IsSolvableTwoComponentIn J (centralizer {z} ⊓ centralizer {u}) ∧
      Nonempty (↥J ⧸ pPrimeCore 2 ↥J ≃* SL(2, ZMod 3)) ∧
      J ≤ L ⊔ (pPrimeCore 2 ↥(centralizer {z} ⊓ centralizer {u})).map
        (centralizer {z} ⊓ centralizer {u}).subtype ∧
      ∀ w : ↥L, w ∈ centralizer {(⟨u, huL⟩ : ↥L)} →
        (QuotientGroup.mk w : ↥L ⧸ pPrimeCore 2 ↥L) ∈ Y → (w : G) ∈ J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu' : orderOf (⟨u, huL⟩ : ↥L) = 2 := by rw [Subgroup.orderOf_mk]; exact hu
  obtain ⟨P, hPle, hPs, hmem, ⟨eP⟩⟩ := F3S7.exists_lift_section_bar hu' hY.1 hY.2.1
  obtain ⟨h1, h2⟩ := F3S7.map_subnormal_centralizer ⟨u, huL⟩ hPle hPs
  obtain ⟨h3, h4⟩ := F3S7.isSubnormal_inf_of_subnormal hL.1 hL.2.1 (centralizer {u}) h1 h2
  let eJ : ↥P ≃* ↥(P.map L.subtype) := P.equivMapOfInjective L.subtype L.subtype_injective
  obtain ⟨hJ, hJe⟩ := F3.isSolvableTwoComponentIn_sup h3 h4
    ((QuotientGroup.congr _ _ eJ.symm (pPrimeCore_map_iso 2 eJ.symm)).trans (eP.trans eY))
  refine ⟨_, hJ, hJe, sup_le_sup_right (map_subtype_le P) _, fun w hw hwY => ?_⟩
  exact mem_sup_left ⟨w, hmem w hw hwY, rfl⟩

variable {z : G} {L : Subgroup G}

theorem S7Config.conj (h : S7Config G z L) (g : G) :
    S7Config G (g * z * g⁻¹) (L.map (MulAut.conj g).toMonoidHom) := by
  have hmap : (centralizer ({z} : Set G)).map (MulAut.conj g).toMonoidHom =
      centralizer {g * z * g⁻¹} := by
    rw [map_centralizer_singleton_mulEquiv, MulAut.conj_apply]
  let eg : ↥L ≃* ↥(L.map (MulAut.conj g).toMonoidHom) :=
    L.equivMapOfInjective _ (MulAut.conj g).injective
  exact ⟨h.simple, h.nonab, h.kProper, h.notCat,
    by rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]; exact h.hz,
    hmap ▸ L35.isTwoComponentIn_map_of_injective _ (MulAut.conj g).injective h.hL,
    ⟨z, h.hzL, rfl⟩,
    isCoverOf_of_mulEquiv (QuotientGroup.congr _ _ eg (pPrimeCore_map_iso 2 eg)) h.hcov,
    T23.isMTypeSchur_of_mulEquiv eg h.hM⟩

theorem S7Config.eq_sup_of_isSolvableTwoComponentIn (hI : S7Inputs) (h : S7Config G z L)
    {u : G} (huL : u ∈ L) (hu : orderOf u = 2)
    (huZ : (QuotientGroup.mk (⟨u, huL⟩ : ↥L) : Bar L) ∉ center (Bar L))
    {Y : Subgroup (Bar L)}
    (hY : IsSolvableTwoComponentIn Y (centralizer {(QuotientGroup.mk ⟨u, huL⟩ : Bar L)}))
    (huY : (QuotientGroup.mk ⟨u, huL⟩ : Bar L) ∈ Y) {K : Subgroup G}
    (hK : IsSolvableTwoComponentIn K (centralizer {z} ⊓ centralizer {u})) (huK : u ∈ K) :
    K = (Y.comap (QuotientGroup.mk' (pPrimeCore 2 ↥L))).map L.subtype ⊓ centralizer {u} ⊔
      (pPrimeCore 2 ↥(centralizer {z} ⊓ centralizer {u})).map
        (centralizer {z} ⊓ centralizer {u}).subtype := by
  have := h.simple
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := centralizer ({z} : Set G) ⊓ centralizer {u} with hMdef
  set OM := (pPrimeCore 2 ↥M).map M.subtype with hOM
  have huz : u ∈ centralizer ({z} : Set G) := h.hL.1 huL
  have hLn := h.normal hI
  have hHN : centralizer ({z} : Set G) ≤ normalizer (L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer h.hL.1).mp hLn
  have hKM : K ≤ M := hK.1
  have hKH : K ≤ centralizer {z} := hKM.trans inf_le_left
  have hKN : K ≤ normalizer (L : Set G) := hKH.trans hHN
  have hON : ∀ x ∈ centralizer ({z} : Set G), ∀ o ∈ (pPrimeCore 2 ↥L).map L.subtype,
      x * o * x⁻¹ ∈ (pPrimeCore 2 ↥L).map L.subtype := fun x hx o ho =>
    (mem_normalizer_iff.mp (UnbalancedGS.normalizer_le_normalizer_map_of_characteristic L
      (pPrimeCore 2 ↥L) (hHN hx)) o).mp ho
  have hOLM : ∀ {o : G}, o ∈ (pPrimeCore 2 ↥L).map L.subtype → o ∈ M → o ∈ OM :=
    fun ho hoM => ⟨⟨_, hoM⟩, mem_pPrimeCore_of_normal
      (fun m hm o ho => hON m (mem_inf.mp hm).1 o ho) (odd_card_pPrimeCore_map L) hoM ho, rfl⟩
  have hKL : GH74.GLS.oPrimeResidualOf 2 K ≤ L := by
    rcases F3S7.lemma221_solvable hu huz hK huK h.hL h.hcov
        (.inl (hKM.trans (inf_le_left.trans hHN))) with h1 | h1
    · exact h1
    · exact absurd (mk_mem_center_of_mem_coreActionKernel huL (h1 huK)) huZ
  set B := L ⊔ K with hBdef
  have hLB : L ≤ B := le_sup_left
  have hKB : K ≤ B := le_sup_right
  have hBH : B ≤ centralizer {z} := sup_le h.hL.1 hKH
  have hX : GH74.GLS.oPrimeResidual 2 ↥B = L.subgroupOf B := by
    have h1 := F3S7.oPrimeResidualOf_sup_eq hKN hKL h.hL.2.2.1
    rw [← h1]
    exact (comap_map_eq_self_of_injective B.subtype_injective _).symm
  let eX : ↥(GH74.GLS.oPrimeResidual 2 ↥B) ≃* ↥L :=
    (MulEquiv.subgroupCongr hX).trans (subgroupOfEquivOfLe hLB)
  have hq : IsTwoQuasisimple ↥(GH74.GLS.oPrimeResidual 2 ↥B) :=
    isTwoQuasisimple_of_mulEquiv eX.symm h.hL.2.2
  have hcovX : IsCoverOf .POmegaOdd 3 3 1 2 (↥(GH74.GLS.oPrimeResidual 2 ↥B) ⧸
      pPrimeCore 2 ↥(GH74.GLS.oPrimeResidual 2 ↥B)) :=
    isCoverOf_of_mulEquiv (QuotientGroup.congr _ _ eX.symm (pPrimeCore_map_iso 2 eX.symm)) h.hcov
  set u' : ↥B := ⟨u, hLB huL⟩ with hu'def
  have hu' : orderOf u' = 2 := by rw [hu'def, Subgroup.orderOf_mk]; exact hu
  set D := B ⊓ centralizer {u} with hDdef
  have hCu : centralizer ({u'} : Set ↥B) = D.subgroupOf B :=
    (inf_centralizer_subgroupOf (hLB huL)).symm
  have hDM : D ≤ M := le_inf (inf_le_left.trans hBH) inf_le_right
  have hKD : K ≤ D := le_inf hKB (hKM.trans inf_le_right)
  have hDeq : D = L ⊓ M ⊔ K := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxB, hxu⟩ := mem_inf.mp hx
      have hxB' : x ∈ ((L ⊔ K : Subgroup G) : Set G) := hxB
      rw [coe_mul_of_right_le_normalizer_left L K hKN] at hxB'
      obtain ⟨l, hl, k, hk, rfl⟩ := hxB'
      have hku : k ∈ centralizer ({u} : Set G) := (mem_inf.mp (hKM hk)).2
      have hlu : l ∈ centralizer ({u} : Set G) := by
        have h1 := mul_mem hxu (inv_mem hku)
        rwa [mul_inv_cancel_right] at h1
      exact mul_mem_sup (mem_inf.mpr ⟨hl, mem_inf.mpr ⟨h.hL.1 hl, hlu⟩⟩) hk
    · exact sup_le (le_inf (inf_le_left.trans hLB) (inf_le_right.trans inf_le_right)) hKD
  have hDs : (D.subgroupOf M).IsSubnormal := by
    rw [hDeq, subgroupOf_sup inf_le_right hKM]
    refine CFSG.GroupTheory.isSubnormal_sup (Normal.isSubnormal ⟨fun n hn g => ?_⟩) hK.2.1
    have hgN : (g : G) ∈ normalizer (L : Set G) := hHN (mem_inf.mp g.2).1
    rw [mem_subgroupOf] at hn ⊢
    refine mem_inf.mpr ⟨?_, (g * n * g⁻¹).2⟩
    simp only [coe_mul, coe_inv]
    exact (mem_normalizer_iff.mp hgN n).mp (mem_inf.mp hn).1
  have hOD : (pPrimeCore 2 ↥D).map D.subtype = OM := by
    rw [F3S7.map_pPrimeCore_of_subnormal hDM hDs]
    have hOK : OM ≤ K := by
      show (pPrimeCore 2 ↥M).map M.subtype ≤ K
      rw [← hK.2.2.1]
      exact map_subtype_le _
    exact inf_eq_right.mpr (hOK.trans hKD)
  have hKD' : IsSolvableTwoComponentIn K D :=
    ⟨hKD, L219.isSubnormal_subgroupOf_of_le hDM hK.2.1, by rw [hOD]; exact hK.2.2.1, hK.2.2.2⟩
  have hK' : IsSolvableTwoComponentIn (K.subgroupOf B) (centralizer {u'}) := by
    rw [hCu]
    exact F3S7.isSolvableTwoComponentIn_subgroupOf hKD inf_le_left hKD'
  have huK' : u' ∈ K.subgroupOf B := huK
  have hu'X : u' ∈ GH74.GLS.oPrimeResidual 2 ↥B := by
    rw [hX]
    exact huL
  have hu'Z : (QuotientGroup.mk (⟨u', hu'X⟩ : ↥(GH74.GLS.oPrimeResidual 2 ↥B)) :
      ↥(GH74.GLS.oPrimeResidual 2 ↥B) ⧸ pPrimeCore 2 ↥(GH74.GLS.oPrimeResidual 2 ↥B)) ∉
      center (↥(GH74.GLS.oPrimeResidual 2 ↥B) ⧸
        pPrimeCore 2 ↥(GH74.GLS.oPrimeResidual 2 ↥B)) := by
    intro hc
    apply huZ
    have h1 := (mem_center_mulEquiv_iff
      (QuotientGroup.congr _ _ eX (pPrimeCore_map_iso 2 eX)) _).mpr hc
    have h3 : (QuotientGroup.congr _ _ eX (pPrimeCore_map_iso 2 eX))
        (QuotientGroup.mk ⟨u', hu'X⟩) = (QuotientGroup.mk ⟨u, huL⟩ : Bar L) := rfl
    rwa [h3] at h1
  obtain ⟨J₁, hJ₁, hKeq, hO2⟩ := hI.l57 ↥B hq 3 1 Nat.prime_three (by norm_num) hcovX u' hu' hu'X
    hu'Z (K.subgroupOf B) hK' huK'
  set J := J₁.map B.subtype with hJdef
  have hA' : GH74.GLS.oPrimeResidual 2 ↥B ⊓ centralizer {u'} =
      (L ⊓ centralizer {u}).subgroupOf B := by
    rw [hX, hCu, hDdef]
    ext x
    simp only [mem_inf, mem_subgroupOf]
    constructor
    · rintro ⟨hxL, -, hxu⟩
      exact ⟨hxL, hxu⟩
    · rintro ⟨hxL, hxu⟩
      exact ⟨hxL, x.2, hxu⟩
  have hJ₁' : IsSolvableTwoComponentIn J₁ ((L ⊓ centralizer {u}).subgroupOf B) := by
    rw [← hA']
    exact hJ₁
  have hJ₁eq : J.subgroupOf B = J₁ := comap_map_eq_self_of_injective B.subtype_injective J₁
  have hJLu : J ≤ L ⊓ centralizer {u} := by
    rintro _ ⟨y, hy, rfl⟩
    exact hJ₁'.1 hy
  have hJs : IsSolvableTwoComponentIn J (L ⊓ centralizer {u}) := by
    refine F3S7.isSolvableTwoComponentIn_of_subgroupOf hJLu (inf_le_left.trans hLB) ?_
    rw [hJ₁eq]
    exact hJ₁'
  have hKeq' : K = OM ⊔ J := by
    have h1 := congrArg (Subgroup.map B.subtype) hKeq
    rw [Subgroup.map_sup, subgroupOf_map_subtype, inf_eq_left.mpr hKB, hCu,
      F3S7.map_pPrimeCore_subgroupOf inf_le_left, hOD] at h1
    exact h1
  have huJ : u ∈ J := by
    have h1 : u' ∈ GH74.GLS.oPrimeResidualOf 2 J₁ := hO2 ▸ F3.mem_oPrimeResidualOf huK' hu'
    exact ⟨u', map_subtype_le _ h1, rfl⟩
  have hJL : J ≤ L := hJLu.trans inf_le_left
  have ht2 : orderOf (⟨u, huL⟩ : ↥L) = 2 := by rw [Subgroup.orderOf_mk]; exact hu
  have hJsL : IsSolvableTwoComponentIn (J.subgroupOf L) (centralizer {(⟨u, huL⟩ : ↥L)}) := by
    rw [← inf_centralizer_subgroupOf huL]
    exact F3S7.isSolvableTwoComponentIn_subgroupOf hJLu inf_le_left hJs
  have hū2 := orderOf_mk_eq_two (odd_card_pPrimeCore_two ↥L) ht2
  have hO : pPrimeCore 2 ↥(centralizer {(QuotientGroup.mk (⟨u, huL⟩ : ↥L) : Bar L)}) = ⊥ :=
    (harris82Lemma411U2Three_holds (Bar L) 3 1 Nat.prime_three (by norm_num) h.hcov _ hū2
      huZ).1
  have hJbar := F3S7.isSolvableTwoComponentIn_map_bar ht2 hO hJsL
  have hzc := mem_center_of_le_centralizer h.hL.1 h.hzL
  have hz' : orderOf (⟨z, h.hzL⟩ : ↥L) = 2 := by rw [Subgroup.orderOf_mk]; exact h.hz
  obtain ⟨-, -, huniq, -⟩ := lemma410c_three (by norm_num) h.hcov
    (mk_mem_center_of_mem_center hzc) (mk_ne_one_of_orderOf_two hz') hū2 huZ
  have hJY : (J.subgroupOf L).map (QuotientGroup.mk' (pPrimeCore 2 ↥L)) = Y :=
    huniq _ _ hJbar hY _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
      ⟨⟨u, huL⟩, huJ, rfl⟩ huY
  rw [hKeq', sup_comm OM J]
  apply le_antisymm
  · refine sup_le_sup_right (fun x hx => ?_) _
    have hxL := hJL hx
    refine mem_inf.mpr ⟨⟨⟨x, hxL⟩, ?_, rfl⟩, (mem_inf.mp (hJLu hx)).2⟩
    rw [SetLike.mem_coe, mem_comap, ← hJY]
    exact ⟨⟨x, hxL⟩, hx, rfl⟩
  · refine sup_le (fun x hx => ?_) le_sup_right
    obtain ⟨⟨l, hl, rfl⟩, hlu⟩ := mem_inf.mp hx
    rw [SetLike.mem_coe, mem_comap, ← hJY] at hl
    obtain ⟨j, hj, hjl⟩ := hl
    have hjl' : (QuotientGroup.mk j : Bar L) = QuotientGroup.mk l := hjl
    have hjo : j⁻¹ * l ∈ pPrimeCore 2 ↥L := QuotientGroup.eq.mp hjl'
    have hjM : (j : G) ∈ M := mem_inf.mpr ⟨h.hL.1 j.2, (mem_inf.mp (hJLu hj)).2⟩
    have hlM : (l : G) ∈ M := mem_inf.mpr ⟨h.hL.1 l.2, hlu⟩
    have ho : (j : G)⁻¹ * l ∈ OM := hOLM ⟨j⁻¹ * l, hjo, rfl⟩ (mul_mem (inv_mem hjM) hlM)
    have h1 : (l : G) = j * ((j : G)⁻¹ * l) := by group
    show (l : G) ∈ J ⊔ OM
    rw [h1]
    exact mul_mem_sup hj ho

theorem S7Config.eq_of_isSolvableTwoComponentIn (hI : S7Inputs) (h : S7Config G z L) {u : G}
    (huL : u ∈ L) (hu : orderOf u = 2)
    (huZ : (QuotientGroup.mk (⟨u, huL⟩ : ↥L) : Bar L) ∉ center (Bar L)) {K K' : Subgroup G}
    (hK : IsSolvableTwoComponentIn K (centralizer {z} ⊓ centralizer {u}))
    (hK' : IsSolvableTwoComponentIn K' (centralizer {z} ⊓ centralizer {u})) (huK : u ∈ K)
    (huK' : u ∈ K') : K = K' := by
  have hzc := mem_center_of_le_centralizer h.hL.1 h.hzL
  have hz' : orderOf (⟨z, h.hzL⟩ : ↥L) = 2 := by rw [Subgroup.orderOf_mk]; exact h.hz
  have hu' : orderOf (⟨u, huL⟩ : ↥L) = 2 := by rw [Subgroup.orderOf_mk]; exact hu
  obtain ⟨-, -, -, hc3⟩ := lemma410c_three (by norm_num) h.hcov
    (mk_mem_center_of_mem_center hzc) (mk_ne_one_of_orderOf_two hz')
    (orderOf_mk_eq_two (odd_card_pPrimeCore_two ↥L) hu') huZ
  obtain ⟨Y, hY, -, huY⟩ := hc3 _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  rw [h.eq_sup_of_isSolvableTwoComponentIn hI huL hu huZ hY huY hK huK,
    h.eq_sup_of_isSolvableTwoComponentIn hI huL hu huZ hY huY hK' huK']

theorem S7Config.exists_z₁ (hI : S7Inputs) (h : S7Config G z L) {S : Subgroup G}
    (hS : IsSylowOf 2 S (centralizer {z})) :
    ∃ z₁ : G, ∃ hz₁L : z₁ ∈ L, z₁ ∈ S ∧ orderOf z₁ = 2 ∧
      (QuotientGroup.mk (⟨z₁, hz₁L⟩ : ↥L) : Bar L) ∉ center (Bar L) ∧
      IsSylowOf 2 (S ⊓ centralizer {z₁}) (centralizer {z} ⊓ centralizer {z₁}) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, _, _, hK, ⟨e₁⟩⟩ := nonempty_mulEquiv_spinSeven_three (by norm_num) h.hcov
  have hK' : Nat.card K = 3 ^ 1 := by rw [hK, pow_one]
  obtain ⟨-, -, -, htt, ht1, ht₀Z, -, -, -, -⟩ := spinZ_facts Nat.prime_three (by norm_num) hK'
  set t₀ := tSeven K with ht₀
  have htb2 : orderOf (e₁.symm t₀) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime (by rw [sq]; exact htt) ht1
  obtain ⟨k, hk2, hk1, hkmk⟩ := T23.exists_involution_lift (H := ↥L) (a := e₁.symm t₀)
    (by have h1 := pow_orderOf_eq_one (e₁.symm t₀); rwa [htb2, sq] at h1)
    (fun h1 => by rw [h1, orderOf_one] at htb2; exact absurd htb2 (by norm_num))
  set t : G := (k : G) with ht
  have htL : t ∈ L := k.2
  have hto : orderOf t = 2 := by
    rw [ht, Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rw [sq, hk2]) hk1
  have htZ : (QuotientGroup.mk (⟨t, htL⟩ : ↥L) : Bar L) ∉ center (Bar L) := by
    have hkt : (⟨t, htL⟩ : ↥L) = k := rfl
    rw [hkt, hkmk]
    intro hc
    apply ht₀Z
    have h1 := (mem_center_mulEquiv_iff e₁ (e₁.symm t₀)).mpr hc
    rwa [MulEquiv.apply_symm_apply] at h1
  have htz : t ∈ centralizer ({z} : Set G) := h.hL.1 htL
  have htt' : t ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.mpr rfl
  have httsq : t ^ 2 ^ 1 = 1 := by rw [pow_one, ← hto, pow_orderOf_eq_one]
  obtain ⟨T₀, hT₀, htT₀⟩ := exists_isSylowOf_le
    (zpowers_le.mpr (mem_inf.mpr ⟨htz, htt'⟩) : zpowers t ≤ centralizer {z} ⊓ centralizer {t})
    (isPGroup_zpowers_of_pow httsq)
  obtain ⟨S₀, hS₀, hT₀S₀⟩ := exists_isSylowOf_le (hT₀.le.trans inf_le_left) hT₀.isPGroup
  obtain ⟨k₀, hk₀, hk₀S⟩ := hS.exists_mem_conj hS₀
  set z₁ := k₀⁻¹ * t * k₀ with hz₁
  have hLn := h.normal hI
  have hz₁L : z₁ ∈ L := by
    have h1 := (normal_subgroupOf_iff h.hL.1).mp hLn t k₀⁻¹ htL (inv_mem hk₀)
    rwa [inv_inv] at h1
  have hz₁S : z₁ ∈ S := (hk₀S t).mp (hT₀S₀ (htT₀ (mem_zpowers t)))
  have hz₁o : orderOf z₁ = 2 := by
    rw [hz₁, show k₀⁻¹ * t * k₀ = MulAut.conj k₀⁻¹ t by rw [MulAut.conj_apply, inv_inv],
      MulEquiv.orderOf_eq]
    exact hto
  have hk₀c : k₀ * z = z * k₀ := mem_centralizer_singleton_iff.mp hk₀
  have hk₀z : k₀⁻¹ * z * k₀ = z := by
    calc k₀⁻¹ * z * k₀ = k₀⁻¹ * (k₀ * z) := by rw [mul_assoc, hk₀c]
      _ = z := by group
  have hk₀z' : k₀ * z * k₀⁻¹ = z := by rw [hk₀c, mul_inv_cancel_right]
  have hz₁Z : (QuotientGroup.mk (⟨z₁, hz₁L⟩ : ↥L) : Bar L) ∉ center (Bar L) := by
    intro hc
    have h1 := h.eq_of_mk_mem_center hz₁L hz₁o hc
    have h2 : t = z := by
      calc t = k₀ * z₁ * k₀⁻¹ := by rw [hz₁]; group
        _ = k₀ * z * k₀⁻¹ := by rw [h1]
        _ = z := hk₀z'
    apply htZ
    have h3 : (⟨t, htL⟩ : ↥L) = ⟨z, h.hzL⟩ := Subtype.ext h2
    rw [h3]
    exact mk_mem_center_of_mem_center (mem_center_of_le_centralizer h.hL.1 h.hzL)
  refine ⟨z₁, hz₁L, hz₁S, hz₁o, hz₁Z, ?_⟩
  set P₁ := T₀.map (MulAut.conj k₀⁻¹).toMonoidHom with hP₁
  have hCmap : (centralizer ({z} : Set G) ⊓ centralizer {t}).map (MulAut.conj k₀⁻¹).toMonoidHom =
      centralizer {z} ⊓ centralizer {z₁} := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj k₀⁻¹).injective, map_centralizer_singleton_mulEquiv,
      map_centralizer_singleton_mulEquiv, MulAut.conj_apply, MulAut.conj_apply, inv_inv, hk₀z]
  have hP₁le : P₁ ≤ S ⊓ centralizer {z₁} := by
    rintro _ ⟨x, hx, rfl⟩
    refine mem_inf.mpr ⟨?_, ?_⟩
    · have h1 := (hk₀S x).mp (hT₀S₀ hx)
      simpa [MulAut.conj_apply] using h1
    · have h1 : (MulAut.conj k₀⁻¹).toMonoidHom x ∈
          (centralizer ({z} : Set G) ⊓ centralizer {t}).map (MulAut.conj k₀⁻¹).toMonoidHom :=
        mem_map_of_mem _ (hT₀.le hx)
      rw [hCmap] at h1
      exact (mem_inf.mp h1).2
  have hP₁syl : IsSylowOf 2 P₁ (centralizer {z} ⊓ centralizer {z₁}) := by
    refine isSylowOf_of_card ?_ ?_
    · rw [← hCmap]
      exact map_mono hT₀.le
    · rw [hP₁, card_map_of_injective (MulAut.conj k₀⁻¹).injective, hT₀.card_eq, ← hCmap,
        card_map_of_injective (MulAut.conj k₀⁻¹).injective]
  have heq := hP₁syl.eq_of_le hP₁le (inf_le_inf_right _ hS.le) (hS.isPGroup.to_inf_left)
  rw [heq]
  exact hP₁syl

end CFSG.ComponentClassification.HarrisLit.T1
