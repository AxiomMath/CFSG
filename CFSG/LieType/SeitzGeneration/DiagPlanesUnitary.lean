module

public import CFSG.LieType.SeitzGeneration.DiagPlanes
public import CFSG.LieType.SeitzGeneration.UnitaryTwoInnerEx
public import CFSG.RankThree.PartOne.CTP.SeitzUToral

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.AGLEmbeddingD2 CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LieType.SeitzGeneration.UnitaryTwo

section Torus

variable {ℓ f n p : ℕ} {K : Type} [Field K]

@[expose] def dsu (hU : UnitaryFieldData ℓ f K) {ζ : Kˣ} (hζp : ζ ^ p = 1) (hpq : p ∣ ℓ ^ f + 1)
    (hn : 5 ≤ n) (k : Fin 3) : unitarySU ℓ f K n :=
  ⟨diagU (wt ζ hn k), torusSU_le_unitarySU hU hpq
    (mem_torusSU_iff.2 ⟨wt ζ hn k, fun i => congrFun (wt_pow hζp hn k) i, prod_wt ζ hn k, rfl⟩)⟩

theorem dsu_comm (hU : UnitaryFieldData ℓ f K) {ζ : Kˣ} (hζp : ζ ^ p = 1)
    (hpq : p ∣ ℓ ^ f + 1) (hn : 5 ≤ n) (a b : Fin 3) :
    Commute (dsu hU hζp hpq hn a) (dsu hU hζp hpq hn b) := by
  apply Subtype.ext
  change diagU (wt ζ hn a) * diagU (wt ζ hn b) = diagU (wt ζ hn b) * diagU (wt ζ hn a)
  rw [diagU_mul, diagU_mul, mul_comm]

theorem dsu_pow (hU : UnitaryFieldData ℓ f K) {ζ : Kˣ} (hζp : ζ ^ p = 1) (hpq : p ∣ ℓ ^ f + 1)
    (hn : 5 ≤ n) (a : Fin 3) : dsu hU hζp hpq hn a ^ p = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  change (diagU (wt ζ hn a)) ^ p = 1
  rw [diagU_pow, wt_pow hζp hn a, diagU_one]

theorem dsu_prod_scalar (hU : UnitaryFieldData ℓ f K) {ζ : Kˣ} (hζp : ζ ^ p = 1)
    (hpq : p ∣ ℓ ^ f + 1) (hn : 5 ≤ n) (hζ : orderOf ζ = p) {i j k : ℤ}
    (h : (dsu hU hζp hpq hn 0 ^ i * dsu hU hζp hpq hn 1 ^ j * dsu hU hζp hpq hn 2 ^ k :
      unitarySU ℓ f K n) ∈ (StatedScalars (Fin n) K).subgroupOf (unitarySU ℓ f K n)) :
    (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j ∧ (p : ℤ) ∣ k := by
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 h
  have e : ∀ (d : Fin n → Kˣ) (m : ℤ), (diagU d : GL (Fin n) K) ^ m = diagU (d ^ m) :=
    fun d m => (map_zpow diagUHom d m).symm
  have hg : ((dsu hU hζp hpq hn 0 ^ i * dsu hU hζp hpq hn 1 ^ j * dsu hU hζp hpq hn 2 ^ k :
      unitarySU ℓ f K n) : GL (Fin n) K) =
      diagU (wt ζ hn 0 ^ i * wt ζ hn 1 ^ j * wt ζ hn 2 ^ k) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_zpow, Subgroup.coe_zpow,
      Subgroup.coe_zpow]
    change (diagU (wt ζ hn 0)) ^ i * (diagU (wt ζ hn 1)) ^ j * (diagU (wt ζ hn 2)) ^ k = _
    rw [e, e, e, diagU_mul, diagU_mul]
  refine scalar_wt hζ hn fun l l' => Units.ext ?_
  have hl : ∀ l : Fin n, ((wt ζ hn 0 ^ i * wt ζ hn 1 ^ j * wt ζ hn 2 ^ k) l : K) = c := fun l => by
    have h1 := congrArg
      (fun g : GL (Fin n) K => ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) l l) (hc.trans hg)
    simp only [diagU_apply_same, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq] at h1
    exact h1.symm
  exact (hl l).trans (hl l').symm

end Torus

section Plane

variable {ℓ f n p : ℕ} {K : Type} [Field K]

theorem zpow_eq_one_of_dvd {G : Type*} [Group G] {a : G} (ha : a ^ p = 1) {i : ℤ}
    (h : (p : ℤ) ∣ i) : a ^ i = 1 :=
  orderOf_dvd_iff_zpow_eq_one.1
    ((Int.natCast_dvd_natCast.2 (orderOf_dvd_of_pow_eq_one ha)).trans h)

theorem exists_plane_psu_diag (hU : UnitaryFieldData ℓ f K) (hn : 5 ≤ n) (hp : p.Prime)
    (hpq : p ∣ ℓ ^ f + 1) (hq : ℓ ^ f ≠ 2) :
    ∃ E : Subgroup (StatedProj (StatedSU n (ℓ ^ f) K)), IsElemAbelian p E ∧
      Nat.card E = p ^ 2 ∧ Subgroup.closure {k : StatedProj (StatedSU n (ℓ ^ f) K) |
        ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  classical
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have : Fact p.Prime := ⟨hp⟩
  have hfin := hU.finite
  have hdvd : p ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hU.card_eq_sq]
    have h1 : (ℓ ^ f) ^ 2 - 1 ^ 2 = (ℓ ^ f + 1) * (ℓ ^ f - 1) := Nat.sq_sub_sq _ _
    rw [one_pow] at h1
    rw [h1]
    exact hpq.mul_right _
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  set a := dsu hU hζp hpq hn 0 with ha
  set b := dsu hU hζp hpq hn 1 with hb
  have hab : Commute a b := dsu_comm hU hζp hpq hn 0 1
  have hap : a ^ p = 1 := dsu_pow hU hζp hpq hn 0
  have hbp : b ^ p = 1 := dsu_pow hU hζp hpq hn 1
  let π : unitarySU ℓ f K (n' + 1) →* StatedProj (StatedSU (n' + 1) (ℓ ^ f) K) :=
    QuotientGroup.mk' ((StatedScalars (Fin (n' + 1)) K).subgroupOf (unitarySU ℓ f K (n' + 1)))
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hind : ∀ i j : ℤ, π (a ^ i * b ^ j) = 1 → (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j := fun i j h => by
    have := dsu_prod_scalar hU hζp hpq hn hζ (i := i) (j := j) (k := 0)
      (by simpa using (QuotientGroup.eq_one_iff _).1 h)
    exact ⟨this.1, this.2.1⟩
  obtain ⟨hE₀, hcard₀⟩ : IsElemAbelian p (Subgroup.closure ({a, b} : Set (unitarySU ℓ f K
      (n' + 1)))) ∧ Nat.card (Subgroup.closure ({a, b} : Set (unitarySU ℓ f K (n' + 1)))) =
      p ^ 2 :=
    plane_of_lifts (MonoidHom.id _) hp hab hap hbp fun i j h => hind i j (by
      have h' : a ^ i * b ^ j = 1 := h
      rw [h', map_one])
  have hgen₀ := CFSG.RankThree.PartOne.CTP.closure_centralizers_unitarySU_of_dvd_add_one hU hp hpq
    hq (Subgroup.closure ({a, b} : Set (unitarySU ℓ f K (n' + 1))))
    (fun x hx y hy => congrArg Subtype.val (hE₀.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)) hE₀.2 hcard₀
  obtain ⟨hE, hcard⟩ := plane_of_lifts π hp hab hap hbp hind
  refine ⟨_, hE, hcard, ?_⟩
  have hmap : (Subgroup.closure ({a, b} : Set (unitarySU ℓ f K (n' + 1)))).map π =
      Subgroup.closure ({π a, π b} : Set _) := by
    rw [MonoidHom.map_closure, Set.image_pair]
  refine closure_centralizers_map π hπsurj
    (X := {x | x ∈ Subgroup.closure ({a, b} : Set (unitarySU ℓ f K (n' + 1))) ∧ x ≠ 1}) ?_ ?_
  · have hset : {g : unitarySU ℓ f K (n' + 1) | ∃ x ∈ {x | x ∈ Subgroup.closure
        ({a, b} : Set (unitarySU ℓ f K (n' + 1))) ∧ x ≠ 1}, g * x = x * g} =
        {g | ∃ x ∈ Subgroup.closure ({a, b} : Set (unitarySU ℓ f K (n' + 1))), x ≠ 1 ∧
          g * x = x * g} := by
      ext g
      simp only [Set.mem_ofPred_eq, and_assoc]
    rw [hset]
    exact hgen₀
  · rintro x ⟨hx, hx1⟩
    refine ⟨fun h1 => hx1 ?_, hmap ▸ Subgroup.mem_map_of_mem π hx⟩
    obtain ⟨i, j, rfl⟩ := exists_zpow_pair_of_mem_closure hab hx
    obtain ⟨hi, hj⟩ := hind i j h1
    rw [zpow_eq_one_of_dvd hap hi, zpow_eq_one_of_dvd hbp hj, one_mul]

end Plane

theorem innerEx_unitary_diag {m : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA m q).Valid) {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ q.card + 1) (hq2 : q.card ≠ 2) (hm : 4 ≤ m)
    (hex : ∃ E : Subgroup (MulAut (Cat ⟨.twistedA m q, hv⟩)), IsElemAbelian p E ∧
      Nat.card E = p ^ 2 ∧ InnerPlane ⟨.twistedA m q, hv⟩ p E) :
    ∃ E : Subgroup (MulAut (Cat ⟨.twistedA m q, hv⟩)), IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
      InnerPlane ⟨.twistedA m q, hv⟩ p E ∧ PlaneGen E := by
  set ℓ := TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA m q, hv⟩ with hℓ
  set f := TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA m q, hv⟩ with hf
  have hU := CFSG.RankThree.PartTwo.Census.unitaryFieldData_galoisField ℓ f
    (TauCeti.ValidLieTypeIndex.fieldExponent_pos ⟨.twistedA m q, hv⟩)
  have : Fact ℓ.Prime := ⟨hU.prime⟩
  have hqcard : ℓ ^ f = q.card := by simp [hℓ, hf, TauCeti.ValidLieTypeIndex.characteristic,
    TauCeti.ValidLieTypeIndex.fieldExponent, TauCeti.PrimePower.card_def]
  have hfin := hU.finite
  let e := CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj m q hv
  have hsimpleP : IsSimpleGroup (StatedProj (StatedSU (m + 1) (ℓ ^ f)
      (GaloisField ℓ (2 * f)))) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU (GaloisField ℓ (2 * f)) ℓ f
      (by rw [hU.card, pow_mul']) (m + 1) (by omega) (by
        intro h32
        obtain ⟨h31, -⟩ := Prod.mk.inj h32
        omega)
  have : IsSimpleGroup (Cat ⟨.twistedA m q, hv⟩) := MulEquiv.isSimpleGroup e
  obtain ⟨E₀, -, hE₀c, hE₀⟩ := hex
  have hinj := conj_injective_of_simple_of_range_ne_bot (K := Cat ⟨.twistedA m q, hv⟩)
    (range_conj_ne_bot_of_inner hp hE₀c hE₀)
  obtain ⟨Ē, hĒ, hĒc, hĒgen⟩ := exists_plane_psu_diag hU (by omega : 5 ≤ m + 1) hp
    (by rw [hqcard]; exact hpq) (by rw [hqcard]; exact hq2)
  exact exists_planeGen_of_model hinj e hĒ hĒc hĒgen

end CFSG.LieType.SeitzGeneration
