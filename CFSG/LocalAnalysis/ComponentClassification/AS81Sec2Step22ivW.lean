module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step24

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FieldFourCover

variable {G : Type} [Group G] [Finite G]

section Quotient

omit [Finite G] in
theorem exists_hom_commGroup_ker {P U : Subgroup G} (hUP : U ≤ P)
    (hc : ∀ p ∈ P, ∀ q ∈ P, p * q * p⁻¹ * q⁻¹ ∈ U) :
    ∃ (Q : Type) (_ : CommGroup Q) (π : ↥P →* Q), ∀ x : ↥P, π x = 1 ↔ (x : G) ∈ U := by
  have hN : (U.subgroupOf P).Normal := ⟨fun u hu p => by
    rw [mem_subgroupOf] at hu ⊢
    have h := U.mul_mem (hc p p.2 u (hUP hu)) hu
    simpa [mul_assoc] using h⟩
  have hcomm : ∀ a b : ↥P ⧸ U.subgroupOf P, a * b = b * a := fun a b => by
    induction a using QuotientGroup.induction_on with
    | H a =>
    induction b using QuotientGroup.induction_on with
    | H b =>
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
    have h := hc (b : G)⁻¹ (P.inv_mem b.2) (a : G)⁻¹ (P.inv_mem a.2)
    convert h using 1
    simp only [coe_mul, coe_inv]
    group
  let : CommGroup (↥P ⧸ U.subgroupOf P) :=
    { (inferInstance : Group (↥P ⧸ U.subgroupOf P)) with mul_comm := hcomm }
  refine ⟨↥P ⧸ U.subgroupOf P, this, QuotientGroup.mk' _, fun x => ?_⟩
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]

end Quotient

@[expose] def sec2W (A E : Subgroup G) (y : G) : Subgroup G :=
  closure {p | p ∈ sec2P E ∧ p * (y * p * y⁻¹) * (y * (y * p * y⁻¹) * y⁻¹) ∈ E ⊓ A}

section Frame

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

variable (h11 : Step11)
  {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
  (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A)))

include h11 hE16 hF hL hodd

theorem mul_self_mem_inf_of_mem_sec2P {p : G} (hp : p ∈ sec2P E) : p * p ∈ E ⊓ A := by
  obtain ⟨hD, T, hT⟩ := exists_pointsData h11 hE16 hF hL hodd
  have hCE := mem_of_mem_centralizer_of_frame hF hL hodd
  have hpN := Sec2.sec2P_le E hp
  have hpp := (hD.sq_mem_and_commutator_mem hT hCE hp hp).1
  by_contra hw
  obtain ⟨Q, hQ, hpQ⟩ := hD.cover _ hpp hw
  have hfix : p * (p * p) * p⁻¹ = p * p := by group
  have hw1 : p * p ≠ 1 := fun h => hw (by rw [h]; exact (E ⊓ A).one_mem)
  have hQQ : rightConjugate Q p = Q := by
    by_contra hne
    have hmem : p * p ∈ rightConjugate Q p ⊓ Q :=
      ⟨(mem_rightConjugate_iff Q p _).mpr (by rw [hfix]; exact hpQ), hpQ⟩
    rw [hD.disj _ (rightConjugate_mem_pointsIn hQ hpN) _ hQ hne, mem_bot] at hmem
    exact hw1 hmem
  have hfixQ : pointsAction R E ⟨p⁻¹, inv_mem hpN⟩ ⟨Q, hQ⟩ = ⟨Q, hQ⟩ := by
    apply Subtype.ext
    rw [coe_pointsAction_apply]
    show rightConjugate Q p⁻¹⁻¹ = Q
    rw [inv_inv, hQQ]
  have hpE' : p⁻¹ ∈ E := hD.mem_of_apply_eq hT hCE (p := ⟨p⁻¹, inv_mem hpN⟩) (inv_mem hp) hfixQ
  have hpE : p ∈ E := by simpa using E.inv_mem hpE'
  apply hw1
  rw [← sq]
  exact hF.elemE.2 p hpE

theorem commutator_mem_inf_of_mem_sec2P {p q : G} (hp : p ∈ sec2P E) (hq : q ∈ sec2P E) :
    p * q * p⁻¹ * q⁻¹ ∈ E ⊓ A := by
  have hPU := sec2P_le_centralizer_inf h11 hE16 hF hL hodd
  have ha := mul_self_mem_inf_of_mem_sec2P h11 hE16 hF hL hodd hp
  have hb := mul_self_mem_inf_of_mem_sec2P h11 hE16 hF hL hodd hq
  have hab := mul_self_mem_inf_of_mem_sec2P h11 hE16 hF hL hodd ((sec2P E).mul_mem hp hq)
  have hc1 : (p * q) * (p * p)⁻¹ = (p * p)⁻¹ * (p * q) :=
    (mem_centralizer_iff.mp (hPU ((sec2P E).mul_mem hp hq)) _ (inv_mem ha)).symm
  have hc2 : (p * q * p) * (q * q)⁻¹ = (q * q)⁻¹ * (p * q * p) :=
    (mem_centralizer_iff.mp (hPU ((sec2P E).mul_mem ((sec2P E).mul_mem hp hq) hp)) _
      (inv_mem hb)).symm
  have key : p * q * p⁻¹ * q⁻¹ = (p * p)⁻¹ * ((q * q)⁻¹ * ((p * q) * (p * q))) := by
    calc p * q * p⁻¹ * q⁻¹ = (p * q) * (p * p)⁻¹ * p * (q * q)⁻¹ * q := by group
      _ = (p * p)⁻¹ * (p * q) * p * (q * q)⁻¹ * q := by rw [hc1]
      _ = (p * p)⁻¹ * ((p * q * p) * (q * q)⁻¹) * q := by group
      _ = (p * p)⁻¹ * ((q * q)⁻¹ * (p * q * p)) * q := by rw [hc2]
      _ = (p * p)⁻¹ * ((q * q)⁻¹ * ((p * q) * (p * q))) := by group
  rw [key]
  exact mul_mem (inv_mem ha) (mul_mem (inv_mem hb) hab)

theorem mem_of_conj_mul_inv_mem_sec2P {y : G} (hyA : y ∈ A)
    (hyU : ∀ u ∈ E ⊓ A, y * u * y⁻¹ = u → u = 1) {p : G} (hp : p ∈ sec2P E)
    (hpy : p⁻¹ * (y * p * y⁻¹) ∈ E) : p ∈ E := by
  obtain ⟨hD, T, hT⟩ := exists_pointsData h11 hE16 hF hL hodd
  have hCE := mem_of_mem_centralizer_of_frame hF hL hodd
  have hPR := sec2P_inf_normalizer_eq hD hT hCE (isPGroup_two_of_isElemAbelian hF.elemE)
  have hpN := Sec2.sec2P_le E hp
  obtain ⟨r, hr, hr1⟩ : ∃ r ∈ R, r ≠ 1 := by
    have hne : R ≠ ⊥ := fun h => by
      have := hF.cardR
      rw [h, card_bot] at this
      omega
    obtain ⟨⟨r, hr⟩, hr1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
    exact ⟨r, hr, fun h => hr1 (Subtype.ext h)⟩
  have hyr : y * r * y⁻¹ = r := by
    rw [mem_centralizer_iff.mp (hF.sylowR.le hr) y hyA, mul_inv_cancel_right]
  set e := p⁻¹ * (y * p * y⁻¹) with he
  have hq : p⁻¹ * r * p ∈ E := by
    have := (mem_normalizer_iff.mp (inv_mem hpN) r).mp (hF.R_le_E hr)
    simpa [mul_assoc] using this
  have hqy : y * (p⁻¹ * r * p) * y⁻¹ = p⁻¹ * r * p := by
    have hyp : y * p * y⁻¹ = p * e := by rw [he]; group
    calc y * (p⁻¹ * r * p) * y⁻¹ = (y * p * y⁻¹)⁻¹ * (y * r * y⁻¹) * (y * p * y⁻¹) := by group
      _ = e⁻¹ * (p⁻¹ * r * p) * e := by rw [hyp, hyr]; group
      _ = e⁻¹ * (e * (p⁻¹ * r * p)) := by rw [mul_assoc, hD.comm _ hq e hpy]
      _ = p⁻¹ * r * p := by group
  have hu : r⁻¹ * p⁻¹ * r * p ∈ E ⊓ A := hD.commutator_mem hT hCE hF.elemE (hF.R_le_E hr) hp
  have hu1 : r⁻¹ * p⁻¹ * r * p = 1 := by
    refine hyU _ hu ?_
    calc y * (r⁻¹ * p⁻¹ * r * p) * y⁻¹ = (y * r * y⁻¹)⁻¹ * (y * (p⁻¹ * r * p) * y⁻¹) := by group
      _ = r⁻¹ * p⁻¹ * r * p := by rw [hyr, hqy]; group
  have hrp : r ∈ rightConjugate R p := by
    rw [mem_rightConjugate_iff]
    have h1 : p⁻¹ * r * p = r := by
      calc p⁻¹ * r * p = r * (r⁻¹ * p⁻¹ * r * p) := by group
        _ = r := by rw [hu1, mul_one]
    have h2 : p * r * p⁻¹ = r := by
      calc p * r * p⁻¹ = p * (p⁻¹ * r * p) * p⁻¹ := by rw [h1]
        _ = r := by group
    rw [h2]
    exact hr
  have hQ : rightConjugate R p = R := by
    by_contra hne
    have hmem : r ∈ rightConjugate R p ⊓ R := ⟨hrp, hr⟩
    rw [hD.disj _ (rightConjugate_mem_pointsIn hD.self_mem hpN) _ hD.self_mem hne, mem_bot] at hmem
    exact hr1 hmem
  rw [← hPR]
  exact ⟨hp, (rightConjugate_eq_self_iff R p).mp hQ⟩

theorem sec2W_facts {y : G} (hyA : y ∈ A) (hyE : y ∈ normalizer (E : Set G))
    (hyU : ∀ u ∈ E ⊓ A, y * u * y⁻¹ = u → u = 1)
    (hy3 : ∀ p ∈ sec2P E, y * y * y * p = p * (y * y * y)) :
    (∀ p : G, p ∈ sec2W A E y ↔
      p ∈ sec2P E ∧ p * (y * p * y⁻¹) * (y * (y * p * y⁻¹) * y⁻¹) ∈ E ⊓ A) ∧
    E ⊓ A ≤ sec2W A E y ∧ sec2W A E y ≤ sec2P E ∧ sec2W A E y ⊓ E = E ⊓ A ∧
    sec2W A E y ⊔ E = sec2P E ∧ sec2P E ≤ normalizer (sec2W A E y : Set G) ∧
    y ∈ normalizer (sec2W A E y : Set G) ∧
    ∀ X : Subgroup G, X ≤ sec2P E → y ∈ normalizer (X : Set G) → X ⊓ E ≤ E ⊓ A →
      X ≤ sec2W A E y := by
  have hR := hF.sylowR
  have hRA : R ≤ centralizer (A : Set G) := hR.le
  have hRA1 : R ⊓ A = ⊥ := inf_eq_bot_of_odd_center hRA hR.isPGroup hodd
  have hEP : E ≤ sec2P E := Sec2.le_sec2P (isPGroup_two_of_isElemAbelian hF.elemE) le_normalizer
    le_rfl
  have hUP : E ⊓ A ≤ sec2P E := inf_le_left.trans hEP
  have hyP : y ∈ normalizer (sec2P E : Set G) := Sec2.normalizer_le_normalizer_sec2P E hyE
  have hyU' : y ∈ normalizer ((E ⊓ A : Subgroup G) : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨hyE, le_normalizer hyA⟩
  obtain ⟨Q, _, π, hπ⟩ := exists_hom_commGroup_ker hUP
    (fun p hp q hq => commutator_mem_inf_of_mem_sec2P h11 hE16 hF hL hodd hp hq)
  let cP : ↥(sec2P E) →* ↥(sec2P E) :=
    ((MulAut.conj y).toMonoidHom.comp (sec2P E).subtype).codRestrict (sec2P E)
      fun x => (mem_normalizer_iff.mp hyP x).mp x.2
  have hcP : ∀ x : ↥(sec2P E), ((cP x : ↥(sec2P E)) : G) = y * x * y⁻¹ := fun x => rfl
  have hc3 : ∀ x : ↥(sec2P E), cP (cP (cP x)) = x := fun x => Subtype.ext (by
    rw [hcP, hcP, hcP]
    have h := hy3 x x.2
    calc y * (y * (y * (x : G) * y⁻¹) * y⁻¹) * y⁻¹ = (y * y * y * x) * (y * y * y)⁻¹ := by group
      _ = x := by rw [h, mul_inv_cancel_right])
  have hsq : ∀ x : ↥(sec2P E), π x * π x = 1 := fun x => by
    rw [← map_mul, hπ]
    exact mul_self_mem_inf_of_mem_sec2P h11 hE16 hF hL hodd x.2
  have hdesc : ∀ a b : ↥(sec2P E), π a = π b → π (cP a) = π (cP b) := fun a b h => by
    have h1 : ((a⁻¹ * b : ↥(sec2P E)) : G) ∈ E ⊓ A := by
      rw [← hπ, map_mul, map_inv, h, inv_mul_cancel]
    have h2 : ((cP (a⁻¹ * b) : ↥(sec2P E)) : G) ∈ E ⊓ A := by
      rw [hcP]
      exact (mem_normalizer_iff.mp hyU' _).mp h1
    rw [← hπ, map_mul, map_inv, map_mul, map_inv] at h2
    exact inv_mul_eq_one.mp h2
  let ε : ↥(sec2P E) →* Q := π * π.comp cP * π.comp (cP.comp cP)
  have hε : ∀ x : ↥(sec2P E), ε x = π (x * cP x * cP (cP x)) := fun x => by
    simp only [ε, MonoidHom.mul_apply, MonoidHom.comp_apply, map_mul]
  have hεG : ∀ x : ↥(sec2P E), ε x = 1 ↔
      (x : G) * (y * x * y⁻¹) * (y * (y * x * y⁻¹) * y⁻¹) ∈ E ⊓ A := fun x => by
    rw [hε, hπ]
    rfl
  have hεcP : ∀ x : ↥(sec2P E), ε (cP x) = ε x := fun x => by
    simp only [ε, MonoidHom.mul_apply, MonoidHom.comp_apply, hc3]
    rw [mul_comm (π (cP x) * π (cP (cP x))) (π x), mul_assoc]
  have hcPv : ∀ x : ↥(sec2P E), π (cP (x * cP x * cP (cP x))) = π (x * cP x * cP (cP x)) :=
    fun x => by
      rw [map_mul, map_mul, hc3, map_mul, map_mul, map_mul, map_mul,
        mul_comm (π (cP x) * π (cP (cP x))) (π x), mul_assoc]
  have hfixε : ∀ v : ↥(sec2P E), π (cP v) = π v → ε v = π v := fun v hv => by
    have h2 : π (cP (cP v)) = π v := (hdesc _ _ hv).trans hv
    rw [hε, map_mul, map_mul, hv, h2, mul_assoc, hsq, mul_one]
  have hvE : ∀ x : ↥(sec2P E), ((x * cP x * cP (cP x) : ↥(sec2P E)) : G) ∈ E := fun x => by
    set v := x * cP x * cP (cP x)
    have h1 : ((v⁻¹ * cP v : ↥(sec2P E)) : G) ∈ E ⊓ A := by
      rw [← hπ, map_mul, map_inv, hcPv x, inv_mul_cancel]
    exact mem_of_conj_mul_inv_mem_sec2P h11 hE16 hF hL hodd hyA hyU v.2 h1.1
  have hmemS : {p : G | p ∈ sec2P E ∧ p * (y * p * y⁻¹) * (y * (y * p * y⁻¹) * y⁻¹) ∈ E ⊓ A} =
      ((ε.ker.map (sec2P E).subtype : Subgroup G) : Set G) := by
    ext p
    constructor
    · rintro ⟨hp, hpε⟩
      exact ⟨⟨p, hp⟩, (hεG ⟨p, hp⟩).mpr hpε, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, (hεG x).mp hx⟩
  have hW : sec2W A E y = ε.ker.map (sec2P E).subtype := by
    rw [sec2W, hmemS, closure_eq]
  have hmemW : ∀ p : G, p ∈ sec2W A E y ↔
      p ∈ sec2P E ∧ p * (y * p * y⁻¹) * (y * (y * p * y⁻¹) * y⁻¹) ∈ E ⊓ A := fun p => by
    rw [hW, ← SetLike.mem_coe, ← hmemS]
    rfl
  have hUW : E ⊓ A ≤ sec2W A E y := fun u hu => by
    rw [hmemW]
    refine ⟨hUP hu, ?_⟩
    have h1 := (mem_normalizer_iff.mp hyU' u).mp hu
    have h2 := (mem_normalizer_iff.mp hyU' _).mp h1
    exact mul_mem (mul_mem hu h1) h2
  have hWP : sec2W A E y ≤ sec2P E := fun p hp => ((hmemW p).mp hp).1
  refine ⟨hmemW, hUW, hWP, ?_, ?_, ?_, ?_, ?_⟩
  ·
    refine le_antisymm (fun e he => ?_) (le_inf hUW inf_le_left)
    obtain ⟨a, ha, r, hr, rfl⟩ := exists_eq_mul_of_le_sup hRA hF.R_le_E hF.E_le he.2
    have hcr : cP ⟨r, hEP (hF.R_le_E hr)⟩ = ⟨r, hEP (hF.R_le_E hr)⟩ := Subtype.ext (by
      rw [hcP]
      show y * r * y⁻¹ = r
      rw [mem_centralizer_iff.mp (hRA hr) y hyA, mul_inv_cancel_right])
    have hεa : ε ⟨a, hUP ha⟩ = 1 := (hεG _).mpr ((hmemW a).mp (hUW ha)).2
    have hεar : ε ⟨a * r, hWP he.1⟩ = 1 := (hεG _).mpr ((hmemW _).mp he.1).2
    have hsplit : (⟨a * r, hWP he.1⟩ : ↥(sec2P E)) =
        ⟨a, hUP ha⟩ * ⟨r, hEP (hF.R_le_E hr)⟩ := rfl
    rw [hsplit, map_mul, hεa, one_mul, hfixε _ (by rw [hcr])] at hεar
    have hrU : r ∈ E ⊓ A := (hπ ⟨r, hEP (hF.R_le_E hr)⟩).mp hεar
    have hr1 : r = 1 := by
      have : r ∈ R ⊓ A := ⟨hr, hrU.2⟩
      rwa [hRA1, mem_bot] at this
    rw [hr1, mul_one]
    exact ha
  ·
    refine le_antisymm (sup_le hWP hEP) fun p hp => ?_
    set x : ↥(sec2P E) := ⟨p, hp⟩
    set v := x * cP x * cP (cP x)
    have hxv : ((x * v⁻¹ : ↥(sec2P E)) : G) ∈ sec2W A E y := by
      rw [hW]
      refine ⟨x * v⁻¹, ?_, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, hfixε v (hcPv x), ← hε,
        mul_inv_cancel]
    have hpe : p = ((x * v⁻¹ : ↥(sec2P E)) : G) * (v : G) := by
      simp only [coe_mul, coe_inv, inv_mul_cancel_right, x]
    rw [hpe]
    exact mul_mem (mem_sup_left hxv) (mem_sup_right (hvE x))
  ·
    intro q hq
    refine AS76b.mem_normalizer_of_map_conj_le ?_
    rintro _ ⟨w, hw, rfl⟩
    have hk := commutator_mem_inf_of_mem_sec2P h11 hE16 hF hL hodd hq (hWP hw)
    have : (MulAut.conj q).toMonoidHom w = (q * w * q⁻¹ * w⁻¹) * w := by
      simp [MulAut.conj_apply]
    rw [this]
    exact mul_mem (hUW hk) hw
  ·
    refine AS76b.mem_normalizer_of_map_conj_le ?_
    rintro _ ⟨w, hw, rfl⟩
    rw [hW] at hw ⊢
    obtain ⟨x, hx, rfl⟩ := hw
    refine ⟨cP x, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, hεcP]
    exact MonoidHom.mem_ker.mp hx
  ·
    intro X hXP hyX hXE x hx
    set x₀ : ↥(sec2P E) := ⟨x, hXP hx⟩
    have h1 : y * x * y⁻¹ ∈ X := (mem_normalizer_iff.mp hyX x).mp hx
    have h2 : y * (y * x * y⁻¹) * y⁻¹ ∈ X := (mem_normalizer_iff.mp hyX _).mp h1
    have hvX : ((x₀ * cP x₀ * cP (cP x₀) : ↥(sec2P E)) : G) ∈ X :=
      mul_mem (mul_mem hx h1) h2
    have hvU := hXE ⟨hvX, hvE x₀⟩
    rw [hmemW]
    exact ⟨hXP hx, hvU⟩

end Frame

end CFSG.ComponentClassification.AS81
