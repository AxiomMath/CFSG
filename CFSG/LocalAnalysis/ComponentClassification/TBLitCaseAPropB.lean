module

public import CFSG.LocalAnalysis.ComponentClassification.TBLitCoreBasics
public import CFSG.LocalAnalysis.ComponentClassification.TBLitQuotSL

public noncomputable section

namespace CFSG.ComponentClassification.TBLit

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.UnbalancingLocal
open scoped commutatorElement Pointwise MatrixGroups

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem map_centralizer_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (u : G) :
    (centralizer ({u} : Set G)).map e.toMonoidHom = centralizer ({e u} : Set H) := by
  ext y
  rw [mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h1 := congrArg e h
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h1
  · intro h
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact h

theorem isPComponent_centralizer_map {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (e : G ≃* H) {u : G} {S : Subgroup G} (hS : S ≤ centralizer ({u} : Set G))
    (h : IsPComponent 2 (S.subgroupOf (centralizer ({u} : Set G)))) :
    S.map e.toMonoidHom ≤ centralizer ({e u} : Set H) ∧
      IsPComponent 2 ((S.map e.toMonoidHom).subgroupOf (centralizer ({e u} : Set H))) := by
  have hC := map_centralizer_mulEquiv e u
  refine ⟨hC ▸ map_mono hS, ?_⟩
  let e' : centralizer ({u} : Set G) ≃* centralizer ({e u} : Set H) :=
    (e.subgroupMap _).trans (MulEquiv.subgroupCongr hC)
  have hmap : (S.subgroupOf (centralizer ({u} : Set G))).map e'.toMonoidHom =
      (S.map e.toMonoidHom).subgroupOf (centralizer ({e u} : Set H)) := by
    ext ⟨y, hy⟩
    constructor
    · rintro ⟨x, hx, hxy⟩
      have h1 : e (x : G) = y := congrArg Subtype.val hxy
      exact ⟨x, hx, h1⟩
    · rintro ⟨x, hx, hxy⟩
      have hxC : x ∈ centralizer ({u} : Set G) := hS hx
      refine ⟨⟨x, hxC⟩, hx, Subtype.ext ?_⟩
      exact hxy
  rw [← hmap]
  exact ((LocalAnalysis.ComponentInitial.p_component_isomorphism_transport 2 Nat.prime_two
    e').1 _).mp h

theorem isPComponent_subgroupOf_map {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (e : G ≃* H) {C S : Subgroup G} (hS : S ≤ C) (h : IsPComponent 2 (S.subgroupOf C)) :
    IsPComponent 2 ((S.map e.toMonoidHom).subgroupOf (C.map e.toMonoidHom)) := by
  let e' : C ≃* C.map e.toMonoidHom := e.subgroupMap C
  have hmap : (S.subgroupOf C).map e'.toMonoidHom =
      (S.map e.toMonoidHom).subgroupOf (C.map e.toMonoidHom) := by
    ext ⟨y, hy⟩
    constructor
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, hx, congrArg Subtype.val hxy⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨⟨x, hS hx⟩, hx, Subtype.ext hxy⟩
  rw [← hmap]
  exact ((LocalAnalysis.ComponentInitial.p_component_isomorphism_transport 2 Nat.prime_two
    e').1 _).mp h

theorem autFixed_quotAutOfChar_surjective {K : Type*} [Group K] [Finite K] (σ : MulAut K)
    (hσ : σ * σ = 1) :
    ∀ q ∈ autFixed (quotAutOfChar (pPrimeCore 2 K) σ),
      ∃ k ∈ autFixed σ, (k : K ⧸ pPrimeCore 2 K) = q := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA : IsPGroup 2 (zpowers σ) := isPGroup_zpowers_of_sq_eq_one (by rw [pow_two, hσ])
  have hN : ∀ g : zpowers σ, ∀ n ∈ pPrimeCore 2 K, ((zpowers σ).subtype g) n ∈ pPrimeCore 2 K :=
    fun g n hn => by
      have h1 := map_mulAut_eq_of_characteristic (pPrimeCore 2 K) ((zpowers σ).subtype g)
      rw [← h1]
      exact mem_map_of_mem _ hn
  have hcop : ¬ 2 ∣ Nat.card (pPrimeCore 2 K) := fun h =>
    Nat.not_coprime_of_dvd_of_dvd one_lt_two dvd_rfl h (pPrimeCore_coprime_card (p := 2))
  have hfix := Semidihedral.Principal.coprime_fixed_point_lifting 2 hA (zpowers σ).subtype
    (pPrimeCore 2 K) hN hcop
  intro q hq
  have hq' : q ∈ {q : K ⧸ pPrimeCore 2 K | ∀ g : zpowers σ,
      Semidihedral.Principal.CoprimeFixedPoint.quotientAction (zpowers σ).subtype
        (pPrimeCore 2 K) hN g q = q} := by
    intro g
    have hq1 : quotAutOfChar (pPrimeCore 2 K) σ q = q := hq
    rcases eq_one_or_eq_of_mem_zpowers (by rw [pow_two, hσ]) g.2 with hg | hg
    · rw [show g = 1 from Subtype.ext hg, map_one]
      rfl
    · rw [show g = ⟨σ, mem_zpowers σ⟩ from Subtype.ext hg]
      induction q using QuotientGroup.induction_on with
      | H x => exact hq1
  rw [hfix] at hq'
  obtain ⟨c, hc, hcq⟩ := hq'
  exact ⟨c, (hc ⟨σ, mem_zpowers σ⟩), hcq⟩

theorem comap_pPrimeCore_of_odd_ker {N R : Type*} [Group N] [Group R] [Finite N] [Finite R]
    (f : N →* R) (hf : Function.Surjective f) (hker : Odd (Nat.card f.ker)) :
    (pPrimeCore 2 R).comap f = pPrimeCore 2 N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm _ (fun x hx => map_pPrimeCore_le f hf (mem_map_of_mem f hx))
  set P := (pPrimeCore 2 R).comap f with hP
  have hPn : P.Normal := (pPrimeCore_normal (p := 2) (G := R)).comap f
  let g : P →* pPrimeCore 2 R := (f.comp P.subtype).codRestrict _ (fun x => x.2)
  have hg : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨⟨x, hy⟩, rfl⟩
  have hkerg : Nat.card g.ker = Nat.card f.ker := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x : P), MonoidHom.mem_ker.mpr
          (congrArg Subtype.val (MonoidHom.mem_ker.mp x.2))⟩
        invFun := fun y => ⟨⟨y, show f y ∈ pPrimeCore 2 R by
            rw [MonoidHom.mem_ker.mp y.2]; exact one_mem _⟩,
          MonoidHom.mem_ker.mpr (Subtype.ext (MonoidHom.mem_ker.mp y.2))⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hcard : Nat.card P = Nat.card g.ker * Nat.card (pPrimeCore 2 R) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective g hg).toEquiv, mul_comm]
  have hodd : Odd (Nat.card P) := by
    rw [hcard, hkerg]
    exact hker.mul (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
  exact le_sSup ⟨hPn, Nat.coprime_two_left.mpr hodd⟩

theorem exists_quotient_pPrimeCore_equiv {N R : Type*} [Group N] [Group R] [Finite N] [Finite R]
    (f : N →* R) (hf : Function.Surjective f) (hker : Odd (Nat.card f.ker)) :
    ∃ e : N ⧸ pPrimeCore 2 N ≃* R ⧸ pPrimeCore 2 R,
      ∀ x : N, e (x : N ⧸ pPrimeCore 2 N) = (f x : R ⧸ pPrimeCore 2 R) := by
  let φ : N →* R ⧸ pPrimeCore 2 R := (QuotientGroup.mk' (pPrimeCore 2 R)).comp f
  have hφ : Function.Surjective φ := (QuotientGroup.mk'_surjective _).comp hf
  have hφker : φ.ker = pPrimeCore 2 N := by
    rw [← comap_pPrimeCore_of_odd_ker f hf hker, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hφker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ), fun x => rfl⟩

abbrev quotImage (M S : Subgroup X) : Subgroup (M ⧸ pPrimeCore 2 M) :=
  (S.subgroupOf M).map (QuotientGroup.mk' (pPrimeCore 2 M))

theorem exists_quotImage_hom {M S : Subgroup X} (hSM : S ≤ M) :
    ∃ ψ : S →* quotImage M S, Function.Surjective ψ ∧
      (∀ x : S, (ψ x : M ⧸ pPrimeCore 2 M) = ((⟨x, hSM x.2⟩ : M) : M ⧸ pPrimeCore 2 M)) ∧
      Odd (Nat.card ψ.ker) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ψ : S →* quotImage M S :=
    { toFun := fun x => ⟨((⟨x, hSM x.2⟩ : M) : M ⧸ pPrimeCore 2 M), ⟨⟨x, hSM x.2⟩, x.2, rfl⟩⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine ⟨ψ, ?_, fun x => rfl, ?_⟩
  · rintro ⟨_, ⟨m, hm, rfl⟩⟩
    exact ⟨⟨m, hm⟩, rfl⟩
  · let ι : ψ.ker →* pPrimeCore 2 M :=
      { toFun := fun x => ⟨⟨(x : S), hSM (x : S).2⟩, by
          have h1 := congrArg Subtype.val (MonoidHom.mem_ker.mp x.2)
          exact (QuotientGroup.eq_one_iff _).mp h1⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hι : Function.Injective ι := by
      intro x y h
      have h' := congrArg (fun z : pPrimeCore 2 M => ((z : M) : X)) h
      exact Subtype.ext (Subtype.ext h')
    exact Odd.of_dvd_nat (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
      (Subgroup.card_dvd_of_injective ι hι)

omit [Finite X] in
theorem oddQuotAction_mem_quotImage {M S : Subgroup X} {g : X}
    (hgM : g ∈ normalizer (M : Set X)) (hgS : g ∈ normalizer (S : Set X))
    {q : M ⧸ pPrimeCore 2 M} (hq : q ∈ quotImage M S) :
    oddQuotAction M ⟨g, hgM⟩ q ∈ quotImage M S := by
  obtain ⟨m, hm, rfl⟩ := hq
  rw [QuotientGroup.mk'_apply, oddQuotAction_mk]
  exact ⟨_, show ((g * m * g⁻¹ : X) ∈ S) from (mem_normalizer_iff.mp hgS m).mp hm, rfl⟩

theorem forall_quotImage_iff {M S : Subgroup X} (hSM : S ≤ M) {g : X}
    (hgM : g ∈ normalizer (M : Set X)) (hgS : g ∈ normalizer (S : Set X)) :
    (∀ q ∈ quotImage M S, oddQuotAction M ⟨g, hgM⟩ q * q⁻¹ ∈
        (pPrimeCore 2 (quotImage M S)).map (quotImage M S).subtype) ↔
      ∀ x ∈ S, ⁅x, g⁆ ∈ oddCoreIn S := by
  obtain ⟨ψ, hψ, hψv, hψk⟩ := exists_quotImage_hom hSM
  have hcomap := comap_pPrimeCore_of_odd_ker ψ hψ hψk
  have hgx : ∀ x ∈ S, g * x * g⁻¹ * x⁻¹ ∈ S := fun x hx =>
    mul_mem ((mem_normalizer_iff.mp hgS x).mp hx) (inv_mem hx)
  have hval : ∀ x (hx : x ∈ S), ((ψ ⟨g * x * g⁻¹ * x⁻¹, hgx x hx⟩ : quotImage M S) :
      M ⧸ pPrimeCore 2 M) = oddQuotAction M ⟨g, hgM⟩ ((ψ ⟨x, hx⟩ : quotImage M S) :
        M ⧸ pPrimeCore 2 M) * ((ψ ⟨x, hx⟩ : quotImage M S) : M ⧸ pPrimeCore 2 M)⁻¹ := by
    intro x hx
    rw [hψv, hψv, oddQuotAction_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    rfl
  constructor
  · intro h x hx
    have h1 := h _ (ψ ⟨x, hx⟩).2
    rw [← hval x hx] at h1
    obtain ⟨y, hy, hyv⟩ := h1
    have h2 : ψ ⟨g * x * g⁻¹ * x⁻¹, hgx x hx⟩ ∈ pPrimeCore 2 (quotImage M S) := by
      rwa [← Subtype.ext hyv]
    have h3 : (⟨g * x * g⁻¹ * x⁻¹, hgx x hx⟩ : S) ∈ pPrimeCore 2 S := by
      rw [← hcomap]
      exact h2
    have h3' : g * x * g⁻¹ * x⁻¹ ∈ oddCoreIn S := ⟨_, h3, rfl⟩
    have h4 := inv_mem h3'
    rwa [show (g * x * g⁻¹ * x⁻¹)⁻¹ = ⁅x, g⁆ by rw [commutatorElement_def]; group] at h4
  · intro h q hq
    obtain ⟨⟨x, hx⟩, hxq⟩ := hψ ⟨q, hq⟩
    have hq' : q = ((ψ ⟨x, hx⟩ : quotImage M S) : M ⧸ pPrimeCore 2 M) :=
      (congrArg Subtype.val hxq).symm
    rw [hq', ← hval x hx]
    have h1 := inv_mem (h x hx)
    rw [show (⁅x, g⁆)⁻¹ = g * x * g⁻¹ * x⁻¹ by rw [commutatorElement_def]; group] at h1
    obtain ⟨y, hy, hyv⟩ := h1
    have hy' : y = ⟨g * x * g⁻¹ * x⁻¹, hgx x hx⟩ := Subtype.ext hyv
    have h2 : ψ y ∈ pPrimeCore 2 (quotImage M S) := by
      rw [← hcomap] at hy
      exact hy
    rw [hy'] at h2
    exact ⟨_, h2, rfl⟩

theorem quotImage_isPComponent_autFixed {M S : Subgroup X} {b : X}
    (hbM : b ∈ normalizer (M : Set X)) (hb : b * b = 1)
    (hS : S ≤ M ⊓ centralizer ({b} : Set X))
    (hSc : IsPComponent 2 (S.subgroupOf (M ⊓ centralizer ({b} : Set X)))) :
    quotImage M S ≤ autFixed (oddQuotAction M ⟨b, hbM⟩) ∧
      IsPComponent 2 ((quotImage M S).subgroupOf (autFixed (oddQuotAction M ⟨b, hbM⟩))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set σ : MulAut M := M.normalizerMonoidHom ⟨b, hbM⟩ with hσ
  have hσv : ∀ m : M, ((σ m : M) : X) = b * m * b⁻¹ := fun m => rfl
  have hσσ : σ * σ = 1 := by
    refine MulEquiv.ext fun m => Subtype.ext ?_
    rw [MulAut.mul_apply, hσv, hσv, MulAut.one_apply]
    calc b * (b * (m : X) * b⁻¹) * b⁻¹ = (b * b) * m * (b * b)⁻¹ := by group
      _ = m := by rw [hb]; group
  have hfixσ : ∀ m : M, m ∈ autFixed σ ↔ (m : X) ∈ centralizer ({b} : Set X) := by
    intro m
    change σ m = m ↔ _
    rw [mem_centralizer_singleton_iff, Subtype.ext_iff, hσv]
    constructor
    · intro h
      calc (m : X) * b = (b * m * b⁻¹) * b := by rw [h]
        _ = b * m := by group
    · intro h
      rw [← h]
      group
  let f : autFixed σ →* autFixed (oddQuotAction M ⟨b, hbM⟩) :=
    { toFun := fun x => ⟨((x : M) : M ⧸ pPrimeCore 2 M), by
        change quotAutOfChar (pPrimeCore 2 M) σ ((x : M) : M ⧸ pPrimeCore 2 M) = _
        rw [quotAutOfChar_mk]
        exact congrArg _ x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Surjective f := by
    rintro ⟨q, hq⟩
    obtain ⟨k, hk, hkq⟩ := autFixed_quotAutOfChar_surjective σ hσσ q hq
    exact ⟨⟨k, hk⟩, Subtype.ext hkq⟩
  have hker : ¬ 2 ∣ Nat.card f.ker := by
    let ι : f.ker →* pPrimeCore 2 M :=
      { toFun := fun x => ⟨((x : autFixed σ) : M), by
          have h1 := congrArg Subtype.val (MonoidHom.mem_ker.mp x.2)
          exact (QuotientGroup.eq_one_iff _).mp h1⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hι : Function.Injective ι := by
      intro x y h
      have h' := congrArg (fun z : pPrimeCore 2 M => ((z : M) : X)) h
      exact Subtype.ext (Subtype.ext (Subtype.ext h'))
    intro h2
    exact Nat.not_coprime_of_dvd_of_dvd one_lt_two dvd_rfl
      (h2.trans (Subgroup.card_dvd_of_injective ι hι)) (pPrimeCore_coprime_card (p := 2))
  let eC : ↥(M ⊓ centralizer ({b} : Set X)) ≃* autFixed σ :=
    { toFun := fun x => ⟨⟨x, (mem_inf.mp x.2).1⟩, (hfixσ _).mpr (mem_inf.mp x.2).2⟩
      invFun := fun y => ⟨((y : M) : X), mem_inf.mpr ⟨(y : M).2, (hfixσ _).mp y.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  have hS' := ((LocalAnalysis.ComponentInitial.p_component_isomorphism_transport 2 Nat.prime_two
    eC).1 _).mp hSc
  have himage := (CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection f hf
    hker).1.mapsTo hS'
  have hmap : ((S.subgroupOf (M ⊓ centralizer ({b} : Set X))).map eC.toMonoidHom).map f =
      (quotImage M S).subgroupOf (autFixed (oddQuotAction M ⟨b, hbM⟩)) := by
    ext ⟨q, hq⟩
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, hxq⟩
      exact ⟨⟨x, (mem_inf.mp x.2).1⟩, hx, congrArg Subtype.val hxq⟩
    · rintro ⟨m, hm, hmq⟩
      have hmb : (m : X) ∈ M ⊓ centralizer ({b} : Set X) := hS hm
      exact ⟨eC ⟨m, hmb⟩, ⟨⟨m, hmb⟩, hm, rfl⟩, Subtype.ext hmq⟩
  refine ⟨?_, hmap ▸ himage⟩
  rintro _ ⟨m, hm, rfl⟩
  have hmC := (hS hm).2
  exact (f ⟨m, (hfixσ m).mpr hmC⟩).2

omit [Finite X] in
theorem quotientPPrimeCoreCongr_conjQuotAction {M J : Subgroup X} (hMJ : M ≤ J)
    [(M.subgroupOf J).Normal] (g : J) (hg : (g : X) ∈ normalizer (M : Set X))
    (q : M.subgroupOf J ⧸ pPrimeCore 2 (M.subgroupOf J)) :
    Correspondence.quotientPPrimeCoreCongr 2 (subgroupOfEquivOfLe hMJ)
        (conjQuotAction (M.subgroupOf J) (pPrimeCore 2 (M.subgroupOf J)) g q) =
      oddQuotAction M ⟨g, hg⟩
        (Correspondence.quotientPPrimeCoreCongr 2 (subgroupOfEquivOfLe hMJ) q) := by
  induction q using QuotientGroup.induction_on with
  | H k => rfl

omit [Finite X] in
theorem oddQuotAction_mul_apply {M : Subgroup X} {g h : X} (hg : g ∈ normalizer (M : Set X))
    (hh : h ∈ normalizer (M : Set X)) (q : M ⧸ pPrimeCore 2 M) :
    oddQuotAction M ⟨g, hg⟩ (oddQuotAction M ⟨h, hh⟩ q) =
      oddQuotAction M ⟨g * h, mul_mem hg hh⟩ q := by
  rw [← MulAut.mul_apply, ← map_mul]
  rfl

omit [Finite X] in
theorem map_center_subtype_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (T : Subgroup G) :
    (center ↥(T.map e.toMonoidHom)).map (T.map e.toMonoidHom).subtype =
      ((center ↥T).map T.subtype).map e.toMonoidHom := by
  have h := map_center_mulEquiv (e.subgroupMap T)
  change (center ↥(T.map (e : G →* H))).map (T.map (e : G →* H)).subtype = _
  rw [← h, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem caseA_propB (hI : TBInputs) {a b γ : X} {S E : Subgroup X}
    (hC : CoreConfig a b γ S E) {M : Subgroup X} (hSM : S ≤ M)
    (hSMc : IsPComponent 2 (S.subgroupOf (M ⊓ centralizer ({b} : Set X))))
    (haM : a ∈ normalizer (M : Set X)) (hEM : E ≤ normalizer (M : Set X))
    (hbM : b ∈ normalizer (M : Set X)) (hbnt : ¬ ∀ m ∈ M, ⁅m, b⁆ ∈ oddCoreIn M)
    (hanM : ¬ ∀ m ∈ M, ⁅m, a⁆ ∈ oddCoreIn M) (henM : ∃ e ∈ E, ¬ ∀ m ∈ M, ⁅m, e⁆ ∈ oddCoreIn M)
    (hconf : IsUnbalancingConfig γ a M E) (hodd : OddLieType (M ⧸ Open.fusionZStar M))
    (hnot : ∀ p f : ℕ, p.Prime → p ≠ 2 → ¬ LieModel (M ⧸ Open.fusionZStar M) .PSL 2 p f) :
    ∃ u : M ⧸ pPrimeCore 2 M, orderOf u = 2 ∧ ∃ S₁ S₂ : Subgroup (M ⧸ pPrimeCore 2 M),
      S₁ ≤ centralizer ({u} : Set _) ∧ IsPComponent 2 (S₁.subgroupOf (centralizer ({u} : Set _))) ∧
      S₂ ≤ centralizer ({u} : Set _) ∧ IsPComponent 2 (S₂.subgroupOf (centralizer ({u} : Set _))) ∧
      (∃ p n : ℕ, ∃ _ : Fact p.Prime, p ≠ 2 ∧ 0 < n ∧
        Nonempty (S₁ ≃* SL(2, GaloisField p n)) ∧ Nonempty (S₂ ≃* SL(2, GaloisField p n))) ∧
      ⁅S₁, S₂⁆ = ⊥ ∧ S₁ ⊓ S₂ = ⊥ ∧
      (center ↥(S₁ ⊔ S₂)).map (S₁ ⊔ S₂).subtype =
        zpowers u ⊔ zpowers ((⟨γ, hSM hC.hγS⟩ : M) : M ⧸ pPrimeCore 2 M) ∧
      (∀ x ∈ S₁, oddQuotAction M ⟨a, haM⟩ x ∈ S₁) ∧ (∀ x ∈ S₂, oddQuotAction M ⟨a, haM⟩ x ∈ S₂) ∧
      (∀ e (he : e ∈ E), ∀ x ∈ S₁, oddQuotAction M ⟨e, hEM he⟩ x ∈ S₁) ∧
      (∀ e (he : e ∈ E), ∀ x ∈ S₂, oddQuotAction M ⟨e, hEM he⟩ x ∈ S₂) ∧
      (∃ x ∈ S₁, oddQuotAction M ⟨a, haM⟩ x ≠ x) ∧ (∃ x ∈ S₂, oddQuotAction M ⟨a, haM⟩ x ≠ x) ∧
      (∃ e, ∃ he : e ∈ E, ∃ x ∈ S₁, oddQuotAction M ⟨e, hEM he⟩ x ≠ x) ∧
      (∃ e, ∃ he : e ∈ E, ∃ x ∈ S₂, oddQuotAction M ⟨e, hEM he⟩ x ≠ x) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, hMγ, hMc, hEa, hEγ, hYa, hYE⟩ := id hconf
  have hMJ : M ≤ hull M a E := le_hull_left M a E
  have haJ : a ∈ hull M a E := mem_hull_elem M a E
  have hEJ : E ≤ hull M a E := le_hull_right M a E
  have hYn : (M.subgroupOf (hull M a E)).Normal := hull_normal hYa.le hYE.le
  obtain ⟨hKq, -, hM4, -, hEρ⟩ := hull_data hconf hodd hnot
  set K := M.subgroupOf (hull M a E) with hK
  set ι := Correspondence.quotientPPrimeCoreCongr 2 (subgroupOfEquivOfLe hMJ) with hι
  have hJM : ∀ g : hull M a E, (g : X) ∈ normalizer (M : Set X) := fun g =>
    UnbalancedLayer.mem_normalizer_of_subgroupOf hMJ (by
      rw [normalizer_eq_top_iff.mpr hYn]
      exact mem_top g)
  have hdict : ∀ (g : hull M a E) (q : K ⧸ pPrimeCore 2 K),
      ι (conjQuotAction K (pPrimeCore 2 K) g q) = oddQuotAction M ⟨g, hJM g⟩ (ι q) :=
    fun g q => quotientPPrimeCoreCongr_conjQuotAction hMJ g (hJM g) q
  have hb2 : b * b = 1 := by rw [← pow_two, ← hC.hb, pow_orderOf_eq_one]
  have ha2 : a * a = 1 := by rw [← pow_two, ← hC.ha, pow_orderOf_eq_one]
  have hφone : ∀ {g : X} (hg : g ∈ normalizer (M : Set X)),
      oddQuotAction M ⟨g, hg⟩ = 1 ↔ ∀ m ∈ M, ⁅m, g⁆ ∈ oddCoreIn M :=
    fun hg => oddQuotAction_eq_one_iff _
  let s : MulAut (K ⧸ pPrimeCore 2 K) := (ι.trans (oddQuotAction M ⟨b, hbM⟩)).trans ι.symm
  have hs : ∀ q, ι (s q) = oddQuotAction M ⟨b, hbM⟩ (ι q) := fun q => by
    change ι (ι.symm _) = _
    rw [MulEquiv.apply_symm_apply]
    rfl
  have hcomm_aut : ∀ {g h : X} (hg : g ∈ normalizer (M : Set X)) (hh : h ∈ normalizer (M : Set X)),
      g * h = h * g → ∀ q, oddQuotAction M ⟨g, hg⟩ (oddQuotAction M ⟨h, hh⟩ q) =
        oddQuotAction M ⟨h, hh⟩ (oddQuotAction M ⟨g, hg⟩ q) := by
    intro g h hg hh hgh q
    rw [oddQuotAction_mul_apply, oddQuotAction_mul_apply]
    congr 2
    exact Subtype.ext hgh
  have hs2 : orderOf s = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · refine MulEquiv.ext fun q => ι.injective ?_
      rw [pow_two, MulAut.mul_apply, hs, hs, MulAut.one_apply, oddQuotAction_mul_apply]
      rw [show (⟨b * b, mul_mem hbM hbM⟩ : normalizer (M : Set X)) = 1 from Subtype.ext hb2,
        map_one, MulAut.one_apply]
    · intro h1
      apply hbnt
      rw [← hφone hbM]
      refine MulEquiv.ext fun q => ?_
      obtain ⟨q', rfl⟩ := ι.surjective q
      rw [← hs, h1, MulAut.one_apply, MulAut.one_apply]
  set t : hull M a E := ⟨a, haJ⟩ with ht
  have ht2 : orderOf (conjQuotAction K (pPrimeCore 2 K) t) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, show t ^ 2 = 1 from Subtype.ext (by rw [pow_two]; exact ha2), map_one]
    · intro h1
      apply hanM
      rw [← hφone haM]
      refine MulEquiv.ext fun q => ?_
      obtain ⟨q', rfl⟩ := ι.surjective q
      rw [← hdict t q', h1, MulAut.one_apply, MulAut.one_apply]
  have hst : s * conjQuotAction K (pPrimeCore 2 K) t = conjQuotAction K (pPrimeCore 2 K) t * s := by
    refine MulEquiv.ext fun q => ι.injective ?_
    rw [MulAut.mul_apply, MulAut.mul_apply, hs, hdict, hdict, hs]
    exact hcomm_aut hbM haM hC.hab.symm _
  have hsY : ∀ y ∈ E.subgroupOf (hull M a E),
      s * conjQuotAction K (pPrimeCore 2 K) y = conjQuotAction K (pPrimeCore 2 K) y * s := by
    intro y hy
    refine MulEquiv.ext fun q => ι.injective ?_
    rw [MulAut.mul_apply, MulAut.mul_apply, hs, hdict, hdict, hs]
    exact hcomm_aut hbM (hJM y) (mem_centralizer_singleton_iff.mp (hC.hE hy).1).symm _
  have hMq : IsQuasisimple (M ⧸ pPrimeCore 2 M) := (isPComponent_data hMγ hMc).2.2
  have hY1 : (E.subgroupOf (hull M a E)).map
      (conjQuotAction K (centralPreimage (pPrimeCore 2 K))) ≠ ⊥ := by
    obtain ⟨e₀, he₀, hne₀⟩ := henM
    have hne := rangeRestrict_ne_one_of_not_trivial hMJ hMq (hEJ he₀) (hEM he₀) hne₀
    intro hbot
    apply hne
    apply Subtype.ext
    have h1 : conjQuotAction K (centralPreimage (pPrimeCore 2 K)) ⟨e₀, hEJ he₀⟩ ∈
        (E.subgroupOf (hull M a E)).map (conjQuotAction K (centralPreimage (pPrimeCore 2 K))) :=
      mem_map_of_mem _ (show (⟨e₀, hEJ he₀⟩ : hull M a E) ∈ E.subgroupOf (hull M a E) from he₀)
    rw [hbot, mem_bot] at h1
    exact h1
  have hSb : S ≤ M ⊓ centralizer ({b} : Set X) := le_inf hSM (hC.hS.trans inf_le_left)
  obtain ⟨hQle, hQc⟩ := quotImage_isPComponent_autFixed hbM hb2 hSb hSMc
  set Q := (quotImage M S).map ι.symm.toMonoidHom with hQ
  have hautFixed : autFixed s = (autFixed (oddQuotAction M ⟨b, hbM⟩)).map ι.symm.toMonoidHom := by
    ext q
    rw [mem_map_equiv, MulEquiv.symm_symm]
    change s q = q ↔ oddQuotAction M ⟨b, hbM⟩ (ι q) = ι q
    rw [← hs]
    exact ι.injective.eq_iff.symm
  have hQs : Q ≤ autFixed s := by
    rw [hautFixed]
    exact map_mono hQle
  have hQsc : IsPComponent 2 (Q.subgroupOf (autFixed s)) := by
    rw [hautFixed]
    exact isPComponent_subgroupOf_map ι.symm hQle hQc
  obtain ⟨ψ, hψ, hψv, hψk⟩ := exists_quotImage_hom hSM
  obtain ⟨eψ, -⟩ := exists_quotient_pPrimeCore_equiv ψ hψ hψk
  obtain ⟨p, n, hpf, hp2, hn, ⟨eS⟩⟩ := hC.hSL
  let θ : Q ≃* quotImage M S :=
    { toFun := fun q => ⟨ι q, by
        have h1 : (q : K ⧸ pPrimeCore 2 K) ∈ (quotImage M S).map ι.symm.toMonoidHom := q.2
        rw [mem_map_equiv, MulEquiv.symm_symm] at h1
        exact h1⟩
      invFun := fun x => ⟨ι.symm x, mem_map_of_mem _ x.2⟩
      left_inv := fun q => Subtype.ext (ι.symm_apply_apply _)
      right_inv := fun x => Subtype.ext (ι.apply_symm_apply _)
      map_mul' := fun _ _ => Subtype.ext (map_mul ι _ _) }
  have eQ : Q ⧸ pPrimeCore 2 Q ≃* SL(2, GaloisField p n) :=
    (Correspondence.quotientPPrimeCoreCongr 2 θ).trans (eψ.symm.trans eS)
  have hιO : ∀ q : K ⧸ pPrimeCore 2 K, q ∈ (pPrimeCore 2 Q).map Q.subtype ↔
      ι q ∈ (pPrimeCore 2 (quotImage M S)).map (quotImage M S).subtype := by
    intro q
    have hiso := pPrimeCore_map_iso 2 θ
    constructor
    · rintro ⟨q', hq', rfl⟩
      exact ⟨θ q', hiso ▸ mem_map_of_mem _ hq', rfl⟩
    · rintro ⟨x, hx, hxq⟩
      rw [← hiso] at hx
      obtain ⟨q'', hq'', rfl⟩ := hx
      refine ⟨q'', hq'', ?_⟩
      apply ι.injective
      exact hxq
  have hγM : γ ∈ M := hSM hC.hγS
  set cγ : M ⧸ pPrimeCore 2 M := ((⟨γ, hγM⟩ : M) : M ⧸ pPrimeCore 2 M) with hcγ
  have hcγZ : cγ ∈ center (M ⧸ pPrimeCore 2 M) := by
    refine map_mem_center_of_surjective (QuotientGroup.mk'_surjective _) ?_
    rw [mem_center_iff]
    intro m
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hMγ m.2))
  have hcγ2 : orderOf cγ = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [hcγ, ← QuotientGroup.mk_pow]
      have hγ2 : (⟨γ, hγM⟩ : M) ^ 2 = 1 := Subtype.ext (by
        change γ ^ 2 = 1
        rw [← hC.hγ, pow_orderOf_eq_one])
      rw [hγ2, QuotientGroup.mk_one]
    · rw [hcγ, Ne, QuotientGroup.eq_one_iff]
      exact not_mem_pPrimeCore_of_orderOf_two (by rw [Subgroup.orderOf_mk]; exact hC.hγ)
  have hcγQ : cγ ∈ quotImage M S := ⟨⟨γ, hγM⟩, hC.hγS, rfl⟩
  have hcZ : ι.symm cγ ∈ center (K ⧸ pPrimeCore 2 K) :=
    map_mem_center_of_surjective (f := ι.symm.toMonoidHom) ι.symm.surjective hcγZ
  have hcQ : ι.symm cγ ∈ Q := mem_map_of_mem _ hcγQ
  have hc2 : orderOf (ι.symm cγ) = 2 := by
    have h1 := orderOf_injective ι.symm.toMonoidHom ι.symm.injective cγ
    exact h1.trans hcγ2
  have hcl : ∀ g : hull M a E, g ∈ closure (insert t
      ((E.subgroupOf (hull M a E) : Subgroup (hull M a E)) : Set (hull M a E))) →
      (g : X) ∈ closure (insert a (E : Set X)) := by
    intro g hg
    have h1 : (closure (insert t ((E.subgroupOf (hull M a E) : Subgroup (hull M a E)) :
        Set (hull M a E)))).map (hull M a E).subtype ≤ closure (insert a (E : Set X)) := by
      rw [MonoidHom.map_closure, closure_le]
      rintro _ ⟨y, hy, rfl⟩
      rcases hy with rfl | hy
      · exact subset_closure (Set.mem_insert _ _)
      · exact subset_closure (Set.mem_insert_of_mem _ hy)
    exact h1 (mem_map_of_mem _ hg)
  have hgS : ∀ g ∈ closure (insert a (E : Set X)), g ∈ normalizer (S : Set X) :=
    fun g hg => (hC.hprop.1 hg).1
  have hconjι : ∀ (g : hull M a E) (x : M ⧸ pPrimeCore 2 M),
      conjQuotAction K (pPrimeCore 2 K) g (ι.symm x) =
        ι.symm (oddQuotAction M ⟨g, hJM g⟩ x) := by
    intro g x
    apply ι.injective
    rw [hdict, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  have hmapQ : ∀ g : hull M a E, (g : X) ∈ closure (insert a (E : Set X)) →
      Q.map (conjQuotAction K (pPrimeCore 2 K) g).toMonoidHom = Q := by
    intro g hg
    have hle : Q.map (conjQuotAction K (pPrimeCore 2 K) g).toMonoidHom ≤ Q := by
      rintro _ ⟨q, ⟨x, hx, rfl⟩, rfl⟩
      change conjQuotAction K (pPrimeCore 2 K) g (ι.symm x) ∈ Q
      rw [hconjι]
      exact mem_map_of_mem _ (oddQuotAction_mem_quotImage (hJM g) (hgS _ hg) hx)
    have hcard : Nat.card (Q.map (conjQuotAction K (pPrimeCore 2 K) g).toMonoidHom) =
        Nat.card Q :=
      card_map_of_injective (by exact (conjQuotAction K (pPrimeCore 2 K) g).injective)
    exact eq_of_le_of_card_ge hle hcard.ge
  have hmapO : ∀ g : hull M a E, (g : X) ∈ closure (insert a (E : Set X)) →
      ((pPrimeCore 2 Q).map Q.subtype).map (conjQuotAction K (pPrimeCore 2 K) g).toMonoidHom =
        (pPrimeCore 2 Q).map Q.subtype := by
    intro g hg
    let θg : Q ≃* Q := ((conjQuotAction K (pPrimeCore 2 K) g).subgroupMap Q).trans
      (MulEquiv.subgroupCongr (hmapQ g hg))
    have h1 := pPrimeCore_map_iso 2 θg
    rw [Subgroup.map_map]
    conv_rhs => rw [← h1, Subgroup.map_map]
    rfl
  have hAPV : ActsProperlyVia (conjQuotAction K (pPrimeCore 2 K)) t (E.subgroupOf (hull M a E)) Q
      ((pPrimeCore 2 Q).map Q.subtype) := by
    refine ⟨fun g hg => ⟨hmapQ g (hcl g hg), hmapO g (hcl g hg)⟩, fun g hg htriv => ?_, ?_⟩
    · have hg' := hcl g hg
      have h1 : ∀ x ∈ quotImage M S, oddQuotAction M ⟨g, hJM g⟩ x * x⁻¹ ∈
          (pPrimeCore 2 (quotImage M S)).map (quotImage M S).subtype := by
        intro x hx
        have h2 := htriv (ι.symm x) (mem_map_of_mem _ hx)
        rwa [hιO, map_mul, map_inv, hdict, MulEquiv.apply_symm_apply] at h2
      have h3 := (forall_quotImage_iff hSM (hJM g) (hgS _ hg')).mp h1
      exact ⟨g, hC.hprop.2.1 _ hg' h3, rfl⟩
    · obtain ⟨e, he, x, hx, hex⟩ := hC.hprop.2.2
      have heS := hgS _ (subset_closure (Set.mem_insert_of_mem a he))
      obtain ⟨q, hq, hqnt⟩ : ∃ q ∈ quotImage M S, oddQuotAction M ⟨e, hEM he⟩ q * q⁻¹ ∉
          (pPrimeCore 2 (quotImage M S)).map (quotImage M S).subtype := by
        by_contra hall
        apply hex
        refine (forall_quotImage_iff hSM (hEM he) heS).mp (fun q hq => ?_) x hx
        by_contra h
        exact hall ⟨q, hq, h⟩
      refine ⟨⟨e, hEJ he⟩, he, ι.symm q, mem_map_of_mem _ hq, ?_⟩
      rw [hιO, map_mul, map_inv, hdict, MulEquiv.apply_symm_apply]
      exact hqnt
  obtain ⟨u, hu2, S₁, S₂, hS₁, hS₁c, hS₂, hS₂c, ⟨p', n', hpf', hp2', hn', ⟨e₁⟩, ⟨e₂⟩⟩, hS12,
    hS12', hcen, hAP₁, hAP₂⟩ := hI.propB (hull M a E) K hKq hM4 t s ht2 hs2
      (E.subgroupOf (hull M a E)) hY1 hEρ hst hsY Q hQs hQsc ⟨p, n, hpf, hp2, hn, ⟨eQ⟩⟩
      (ι.symm cγ) hcZ hcQ hc2 hAPV
  have htcl : t ∈ closure (insert t
      ((E.subgroupOf (hull M a E) : Subgroup (hull M a E)) : Set (hull M a E))) :=
    subset_closure (Set.mem_insert _ _)
  have hecl : ∀ e (he : e ∈ E), (⟨e, hEJ he⟩ : hull M a E) ∈ closure (insert t
      ((E.subgroupOf (hull M a E) : Subgroup (hull M a E)) : Set (hull M a E))) :=
    fun e he => subset_closure (Set.mem_insert_of_mem _ (show (⟨e, hEJ he⟩ : hull M a E) ∈
      E.subgroupOf (hull M a E) from he))
  have hnorm : ∀ {T : Subgroup (K ⧸ pPrimeCore 2 K)}
      (hT : ActsProperlyVia (conjQuotAction K (pPrimeCore 2 K)) t (E.subgroupOf (hull M a E)) T ⊥)
      (g : hull M a E) (hg : g ∈ closure (insert t
        ((E.subgroupOf (hull M a E) : Subgroup (hull M a E)) : Set (hull M a E)))),
      ∀ x ∈ T.map ι.toMonoidHom, oddQuotAction M ⟨g, hJM g⟩ x ∈ T.map ι.toMonoidHom := by
    intro T hT g hg x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have h1 : conjQuotAction K (pPrimeCore 2 K) g y ∈ T := by
      rw [← (hT.1 g hg).1]
      exact mem_map_of_mem _ hy
    change oddQuotAction M ⟨g, hJM g⟩ (ι y) ∈ T.map ι.toMonoidHom
    rw [← hdict]
    exact mem_map_of_mem _ h1
  have hEodd : Odd (Nat.card E) := Nat.coprime_two_left.mp
    ((coprime_card_oddCentralizerCore a).coprime_dvd_right (card_dvd_of_le hC.hEa))
  have hant : ∀ {T : Subgroup (K ⧸ pPrimeCore 2 K)}
      (hT : ActsProperlyVia (conjQuotAction K (pPrimeCore 2 K)) t (E.subgroupOf (hull M a E)) T ⊥),
      ∃ x ∈ T.map ι.toMonoidHom, oddQuotAction M ⟨a, haM⟩ x ≠ x := by
    intro T hT
    by_contra hall
    obtain ⟨y, hy, hty⟩ := hT.2.1 t htcl (fun x hx => by
      have h1 : oddQuotAction M ⟨a, haM⟩ (ι x) = ι x := by
        by_contra h
        exact hall ⟨ι x, mem_map_of_mem _ hx, h⟩
      rw [mem_bot, mul_inv_eq_one]
      apply ι.injective
      rw [hdict]
      exact h1)
    have hy2 : orderOf (conjQuotAction K (pPrimeCore 2 K) y) ∣ Nat.card E := by
      refine (orderOf_map_dvd _ y).trans ?_
      rw [← Subgroup.orderOf_coe y, ← Subgroup.orderOf_mk (y : X) hy]
      exact orderOf_dvd_natCard _
    rw [← hty, ht2] at hy2
    exact (Nat.not_even_iff_odd.mpr hEodd) (even_iff_two_dvd.mpr hy2)
  have hent : ∀ {T : Subgroup (K ⧸ pPrimeCore 2 K)}
      (hT : ActsProperlyVia (conjQuotAction K (pPrimeCore 2 K)) t (E.subgroupOf (hull M a E)) T ⊥),
      ∃ e, ∃ he : e ∈ E, ∃ x ∈ T.map ι.toMonoidHom, oddQuotAction M ⟨e, hEM he⟩ x ≠ x := by
    intro T hT
    obtain ⟨y, hy, x, hx, hxy⟩ := hT.2.2
    refine ⟨y, hy, ι x, mem_map_of_mem _ hx, fun h => hxy ?_⟩
    rw [mem_bot, mul_inv_eq_one]
    apply ι.injective
    rw [hdict]
    exact h
  obtain ⟨hS₁', hS₁c'⟩ := isPComponent_centralizer_map ι hS₁ hS₁c
  obtain ⟨hS₂', hS₂c'⟩ := isPComponent_centralizer_map ι hS₂ hS₂c
  have hu2' : orderOf (ι u) = 2 := (orderOf_injective ι.toMonoidHom ι.injective u).trans hu2
  have hcomm' : ⁅S₁.map ι.toMonoidHom, S₂.map ι.toMonoidHom⁆ = ⊥ := by
    rw [← map_commutator, hS12, Subgroup.map_bot]
  have hinf' : S₁.map ι.toMonoidHom ⊓ S₂.map ι.toMonoidHom = ⊥ := by
    rw [← Subgroup.map_inf_eq S₁ S₂ ι.toMonoidHom ι.injective, hS12', Subgroup.map_bot]
  have hcen' : (center ↥(S₁.map ι.toMonoidHom ⊔ S₂.map ι.toMonoidHom)).map
      (S₁.map ι.toMonoidHom ⊔ S₂.map ι.toMonoidHom).subtype =
        zpowers (ι u) ⊔ zpowers cγ := by
    rw [← Subgroup.map_sup, map_center_subtype_mulEquiv ι, hcen, Subgroup.map_sup,
      MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    change zpowers (ι u) ⊔ zpowers (ι (ι.symm cγ)) = _
    rw [MulEquiv.apply_symm_apply]
  have he₁' : Nonempty (S₁.map ι.toMonoidHom ≃* SL(2, GaloisField p' n')) :=
    ⟨(ι.subgroupMap S₁).symm.trans e₁⟩
  have he₂' : Nonempty (S₂.map ι.toMonoidHom ≃* SL(2, GaloisField p' n')) :=
    ⟨(ι.subgroupMap S₂).symm.trans e₂⟩
  have ha₁ : ∀ x ∈ S₁.map ι.toMonoidHom, oddQuotAction M ⟨a, haM⟩ x ∈ S₁.map ι.toMonoidHom :=
    hnorm hAP₁ t htcl
  have hE₁ : ∀ e (he : e ∈ E), ∀ x ∈ S₁.map ι.toMonoidHom,
      oddQuotAction M ⟨e, hEM he⟩ x ∈ S₁.map ι.toMonoidHom := by
    intro e he
    exact hnorm hAP₁ ⟨e, hEJ he⟩ (hecl e he)
  have ha₂ : ∀ x ∈ S₂.map ι.toMonoidHom, oddQuotAction M ⟨a, haM⟩ x ∈ S₂.map ι.toMonoidHom :=
    hnorm hAP₂ t htcl
  have hE₂ : ∀ e (he : e ∈ E), ∀ x ∈ S₂.map ι.toMonoidHom,
      oddQuotAction M ⟨e, hEM he⟩ x ∈ S₂.map ι.toMonoidHom := by
    intro e he
    exact hnorm hAP₂ ⟨e, hEJ he⟩ (hecl e he)
  exact ⟨ι u, hu2', S₁.map ι.toMonoidHom, S₂.map ι.toMonoidHom, hS₁', hS₁c', hS₂', hS₂c',
    ⟨p', n', hpf', hp2', hn', he₁', he₂'⟩, hcomm', hinf', hcen', ha₁, ha₂, hE₁, hE₂,
    hant hAP₁, hant hAP₂, hent hAP₁, hent hAP₂⟩

end CFSG.ComponentClassification.TBLit
