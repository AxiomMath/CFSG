module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95I1921SixFin
public import CFSG.LocalAnalysis.GLTheoremB.Prop95I1921Fam
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A6Aut

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95I1921

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Parts
open CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts

section APD6sec

@[expose] noncomputable def conjEquiv6 : ↥A6Models.autA6 ≃* MulAut ↥A6Models.psl29 :=
  MulEquiv.ofBijective (MonoidHom.mk' DoubleA3.conjAut fun a b => MulEquiv.ext fun x =>
    Subtype.ext (by
      show ((a : P10) * (b : P10)) * (x : P10) * ((a : P10) * (b : P10))⁻¹ =
        (a : P10) * ((b : P10) * (x : P10) * (b : P10)⁻¹) * (a : P10)⁻¹
      group))
    ⟨DoubleA3.conjAut_injective, DoubleA3.conjAut_surjective⟩

theorem conjEquiv6_apply (a : ↥A6Models.autA6) (x : ↥A6Models.psl29) :
    ((conjEquiv6 a x : ↥A6Models.psl29) : P10) = (a : P10) * (x : P10) * (a : P10)⁻¹ := rfl

structure APD6 {X : Type} [Group X] (K : Subgroup X)
    (ε : (↥K ⧸ Subgroup.center ↥K) ≃* ↥A6Models.psl29) where
  θ : MulAut ↥K →* P10
  inj : Function.Injective θ
  mem : ∀ φ, θ φ ∈ A6Models.autA6
  ind : ∀ (φ : MulAut ↥K) (a : ↥K),
    ((ε (QuotientGroup.mk (φ a)) : ↥A6Models.psl29) : P10) =
      θ φ * ((ε (QuotientGroup.mk a) : ↥A6Models.psl29) : P10) * (θ φ)⁻¹
  inner : ∀ k : ↥K, θ (MulAut.conj k) = ((ε (QuotientGroup.mk k) : ↥A6Models.psl29) : P10)

theorem exists_apd6 {X : Type} [Group X] {K : Subgroup X} (hperf : commutator ↥K = ⊤)
    (ε : (↥K ⧸ Subgroup.center ↥K) ≃* ↥A6Models.psl29) : Nonempty (APD6 K ε) := by
  let θ' : MulAut ↥K →* ↥A6Models.autA6 :=
    conjEquiv6.symm.toMonoidHom.comp ((MulAut.congr ε).toMonoidHom.comp quotAutOfCentreHom)
  have hθ' : ∀ φ : MulAut ↥K, conjEquiv6 (θ' φ) = MulAut.congr ε (quotAutOfCentre φ) := by
    intro φ
    exact conjEquiv6.apply_symm_apply (MulAut.congr ε (quotAutOfCentre φ))
  have hind : ∀ (φ : MulAut ↥K) (a : ↥K),
      ((ε (QuotientGroup.mk (φ a)) : ↥A6Models.psl29) : P10) =
        ((θ' φ : ↥A6Models.autA6) : P10) * ((ε (QuotientGroup.mk a) : ↥A6Models.psl29) : P10) *
          ((θ' φ : ↥A6Models.autA6) : P10)⁻¹ := by
    intro φ a
    have h := congrArg (fun f : MulAut ↥A6Models.psl29 =>
      ((f (ε (QuotientGroup.mk a)) : ↥A6Models.psl29) : P10)) (hθ' φ)
    simp only [conjEquiv6_apply, MulAut.congr_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply] at h
    rw [h, quotAutOfCentre_mk]
  refine ⟨⟨A6Models.autA6.subtype.comp θ', ?_, fun φ => (θ' φ).2, fun φ a => hind φ a, ?_⟩⟩
  · rw [injective_iff_map_eq_one]
    intro φ hφ
    have h1 : θ' φ = 1 := Subtype.ext hφ
    have h2 : quotAutOfCentre φ = 1 := by
      apply (MulAut.congr ε).injective
      rw [← hθ' φ, h1, map_one, map_one]
    refine eq_one_of_forall_mk_eq_aut hperf φ fun x => ?_
    have h3 := congrArg (fun ψ : MulAut (↥K ⧸ Subgroup.center ↥K) => ψ (QuotientGroup.mk x)) h2
    simpa [quotAutOfCentre_mk] using h3
  · intro k
    have hmem : ((ε (QuotientGroup.mk k) : ↥A6Models.psl29) : P10) ∈ A6Models.autA6 :=
      psl29_le_autA6 (ε (QuotientGroup.mk k)).2
    have h1 : θ' (MulAut.conj k) = ⟨_, hmem⟩ := by
      apply conjEquiv6.injective
      rw [hθ']
      apply MulEquiv.ext
      intro y
      apply Subtype.ext
      rw [conjEquiv6_apply]
      obtain ⟨q, rfl⟩ := ε.surjective y
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
        quotAutOfCentre_mk]
      simp
    show ((θ' (MulAut.conj k) : ↥A6Models.autA6) : P10) = _
    rw [h1]

end APD6sec

open scoped IsMulCommutative in
theorem not_isMulCommutative_sylow_of_perfect' {X : Type*} [Group X] [Finite X] {p : ℕ}
    [hp : Fact p.Prime] (hX : commutator X = ⊤) {z : X} (hz : z ∈ Subgroup.center X)
    (hzp : orderOf z = p) (S : Sylow p X) : ¬ IsMulCommutative (S : Subgroup X) := by
  intro hS
  have : IsMulCommutative (S : Subgroup X) := hS
  have hzS : z ∈ (S : Subgroup X) := by
    have hN : (Subgroup.zpowers z).Normal :=
      Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hz)
    have hP : IsPGroup p (Subgroup.zpowers z) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzp, pow_one])
    exact hP.le_sylow_of_normal S (Subgroup.mem_zpowers z)
  set ϕ := MonoidHom.transfer (MonoidHom.id (S : Subgroup X)) with hϕ
  have key : ∀ (k : ℕ) (g₀ : X), g₀⁻¹ * z ^ k * g₀ ∈ (S : Subgroup X) →
      g₀⁻¹ * z ^ k * g₀ = z ^ k := fun k g₀ _ => by
    have hzk : z ^ k ∈ Subgroup.center X := Subgroup.pow_mem _ hz k
    rw [mul_assoc, ← Subgroup.mem_center_iff.mp hzk g₀, ← mul_assoc, inv_mul_cancel, one_mul]
  have h1 := MonoidHom.transfer_eq_pow (MonoidHom.id (S : Subgroup X)) z key
  have h2 : ϕ z = 1 := by
    have hzc : z ∈ commutator X := hX ▸ Subgroup.mem_top z
    exact Abelianization.commutator_subset_ker ϕ hzc
  rw [h2] at h1
  have h3 : z ^ (S : Subgroup X).index = 1 := by
    have := congrArg Subtype.val h1
    simpa using this.symm
  have h4 := orderOf_dvd_of_pow_eq_one h3
  rw [hzp] at h4
  exact S.not_dvd_index h4

section ThreeA6

variable {Q : Type} [Group Q]

theorem pow_three_of_mem_center (hZ : Nat.card (Subgroup.center (Q)) = 3) {z : Q}
    (hz : z ∈ Subgroup.center (Q)) : z ^ 3 = 1 := by
  have h := pow_card_eq_one' (x := (⟨z, hz⟩ : Subgroup.center (Q)))
  rw [hZ] at h
  exact congrArg Subtype.val h

theorem commutator_mul_center {X : Type*} [Group X] {z₁ z₂ : X} (h1 : z₁ ∈ Subgroup.center X)
    (h2 : z₂ ∈ Subgroup.center X) (a b : X) :
    (z₁ * a) * (z₂ * b) * (z₁ * a)⁻¹ * (z₂ * b)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have c1 := Subgroup.mem_center_iff.mp h1
  have c2 := Subgroup.mem_center_iff.mp h2
  calc (z₁ * a) * (z₂ * b) * (z₁ * a)⁻¹ * (z₂ * b)⁻¹
      = z₁ * (a * z₂ * b * a⁻¹) * z₁⁻¹ * b⁻¹ * z₂⁻¹ := by group
    _ = (a * z₂ * b * a⁻¹) * z₁ * z₁⁻¹ * b⁻¹ * z₂⁻¹ := by rw [← c1 (a * z₂ * b * a⁻¹)]
    _ = a * z₂ * (b * a⁻¹ * b⁻¹) * z₂⁻¹ := by group
    _ = z₂ * a * (b * a⁻¹ * b⁻¹) * z₂⁻¹ := by rw [c2 a]
    _ = z₂ * (a * b * a⁻¹ * b⁻¹) * z₂⁻¹ := by group
    _ = (a * b * a⁻¹ * b⁻¹) * z₂ * z₂⁻¹ := by rw [← c2 (a * b * a⁻¹ * b⁻¹)]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem exists_mem_center_ne_one (hZ : Nat.card (Subgroup.center (Q)) = 3) :
    ∃ z ∈ Subgroup.center (Q), z ≠ 1 := by
  by_contra h
  push Not at h
  have : Subsingleton (Subgroup.center (Q)) :=
    ⟨fun a b => Subtype.ext ((h a a.2).trans (h b b.2).symm)⟩
  rw [Nat.card_of_subsingleton (1 : Subgroup.center (Q))] at hZ
  omega

theorem not_commute_of_lifts [Finite Q] (hperf : commutator (Q) = ⊤)
    (hZ : Nat.card (Subgroup.center (Q)) = 3) (hcard : Nat.card (Q) = 1080)
    (ψ6 : Q ⧸ Subgroup.center (Q) ≃* ↥A6Models.psl29) {q₁ q₂ : Q}
    (hq₁ : (q₁ : Q ⧸ Subgroup.center (Q)) ^ 3 = 1) (hq₂ : (q₂ : Q ⧸ Subgroup.center (Q)) ^ 3 = 1)
    (hx1 : ((ψ6 (q₁ : Q ⧸ Subgroup.center (Q)) : ↥A6Models.psl29) : P10) ≠ 1)
    (hcomm : ((ψ6 (q₁ : Q ⧸ Subgroup.center (Q)) : ↥A6Models.psl29) : P10) *
        (ψ6 (q₂ : Q ⧸ Subgroup.center (Q)) : P10) =
      (ψ6 (q₂ : Q ⧸ Subgroup.center (Q)) : P10) *
        (ψ6 (q₁ : Q ⧸ Subgroup.center (Q)) : P10))
    (hn : ((ψ6 (q₂ : Q ⧸ Subgroup.center (Q)) : ↥A6Models.psl29) : P10) ∉
      Subgroup.zpowers ((ψ6 (q₁ : Q ⧸ Subgroup.center (Q)) : ↥A6Models.psl29) :
        P10)) :
    q₁ * q₂ ≠ q₂ * q₁ := by
  intro hq
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Zc := Subgroup.center (Q) with hZc
  set x₁ : P10 := ((ψ6 (q₁ : Q ⧸ Zc) : ↥A6Models.psl29) : P10) with hx₁
  set x₂ : P10 := ((ψ6 (q₂ : Q ⧸ Zc) : ↥A6Models.psl29) : P10) with hx₂
  set k : Set (Q) := {q₁, q₂} ∪ (Zc : Set (Q)) with hk
  have hkc : k.Pairwise Commute := by
    intro a ha b hb _
    have hcen : ∀ {u v : Q}, v ∈ Zc → Commute u v := fun {u v} hv =>
      (Subgroup.mem_center_iff.mp hv u)
    rcases ha with ha | ha
    · rcases hb with hb | hb
      · rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact Commute.refl _
        · exact hq
        · exact hq.symm
        · exact Commute.refl _
      · exact hcen hb
    · exact (hcen ha).symm
  set P := Subgroup.closure k with hP
  have hPc : IsMulCommutative P := Subgroup.isMulCommutative_closure hkc
  have hlift9 : ∀ q : Q, (q : Q ⧸ Subgroup.center (Q)) ^ 3 = 1 → q ^ 9 = 1 := by
    intro q hq
    have hq3 : q ^ 3 ∈ Subgroup.center (Q) := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
      exact hq
    rw [show (9 : ℕ) = 3 * 3 by norm_num, pow_mul]
    exact pow_three_of_mem_center hZ hq3
  have hP3 : ∀ p ∈ P, p ^ 9 = 1 := by
    intro p hp
    induction hp using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with (rfl | rfl) | hx
      · exact hlift9 _ hq₁
      · exact hlift9 _ hq₂
      · rw [show (9 : ℕ) = 3 * 3 by norm_num, pow_mul, pow_three_of_mem_center hZ hx, one_pow]
    | one => simp
    | mul x y hx hy ihx ihy =>
      have hxy : Commute x y := by
        have := hPc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
        exact congrArg Subtype.val this
      rw [hxy.mul_pow, ihx, ihy, one_mul]
    | inv x hx ih => rw [inv_pow, ih, inv_one]
  have hP3g : IsPGroup 3 P := fun p => ⟨2, Subtype.ext (by simpa using hP3 p p.2)⟩
  set f : ↥P →* ↥A6Models.psl29 :=
    ψ6.toMonoidHom.comp ((QuotientGroup.mk' Zc).comp P.subtype) with hf
  have hZP : Zc ≤ P := fun z hz => Subgroup.subset_closure (Or.inr hz)
  have hker : Zc.subgroupOf P ≤ f.ker := by
    intro z hz
    rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, MonoidHom.comp_apply,
      Subgroup.coe_subtype, QuotientGroup.mk'_apply,
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mp hz)]
    simp
  have hkerc : 3 ≤ Nat.card f.ker := by
    have h := Subgroup.card_le_of_le hker
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZP).toEquiv, hZ] at h
  have hq₁P : q₁ ∈ P := Subgroup.subset_closure (Or.inl (Or.inl rfl))
  have hq₂P : q₂ ∈ P := Subgroup.subset_closure (Or.inl (Or.inr rfl))
  have hrange : Subgroup.closure ({x₁, x₂} : Set P10) ≤ f.range.map A6Models.psl29.subtype := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact ⟨f ⟨q₁, hq₁P⟩, ⟨⟨q₁, hq₁P⟩, rfl⟩, rfl⟩
    · exact ⟨f ⟨q₂, hq₂P⟩, ⟨⟨q₂, hq₂P⟩, rfl⟩, rfl⟩
  have hx₁3 : x₁ ^ 3 = 1 := by
    rw [hx₁, ← Subgroup.coe_pow, ← map_pow, hq₁]
    simp
  have hx₂3 : x₂ ^ 3 = 1 := by
    rw [hx₂, ← Subgroup.coe_pow, ← map_pow, hq₂]
    simp
  have h9 := CFSG.RankThree.PartTwo.Sec15.Push153B.A6.card_closure_pair (ψ6 (q₁ : Q ⧸ Zc)).2 hx₁3 hx1
    (ψ6 (q₂ : Q ⧸ Zc)).2 hx₂3 hcomm.symm hn
  have hrangec : 9 ≤ Nat.card f.range := by
    have h := Subgroup.card_le_of_le hrange
    rwa [h9, Subgroup.card_map_of_injective Subtype.val_injective] at h
  have hPcard : 27 ≤ Nat.card P := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv] at h1
    rw [h1]
    nlinarith
  obtain ⟨n, hn'⟩ := IsPGroup.iff_card.mp hP3g
  have hdvd : 3 ^ n ∣ 1080 := by
    rw [← hn', ← hcard]
    exact Subgroup.card_subgroup_dvd_card P
  have hn3 : n = 3 := by
    have h27 : 27 ≤ 3 ^ n := hn' ▸ hPcard
    have hle : n ≤ 3 := by
      by_contra hlt
      have : 3 ^ 4 ∣ 1080 := (pow_dvd_pow 3 (by omega)).trans hdvd
      norm_num at this
    have hge : 3 ≤ n := by
      by_contra hlt
      have : 3 ^ n ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    omega
  have hfac : (Nat.card (Q)).factorization 3 = 3 := by
    rw [hcard, show (1080 : ℕ) = 3 ^ 3 * 40 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Nat.Prime.factorization_pow
        Nat.prime_three, Finsupp.add_apply, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]
  let PS : Sylow 3 (Q) := Sylow.ofCard P (by rw [hn', hn3, hfac])
  obtain ⟨z, hz, hz1⟩ := exists_mem_center_ne_one hZ
  have hzo : orderOf z = 3 := by
    have hd : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one (pow_three_of_mem_center hZ hz)
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hz1
    · exact h
  exact not_isMulCommutative_sylow_of_perfect' hperf hz hzo PS hPc

theorem mem_m10_of_fixes_center [Finite Q] (hperf : commutator Q = ⊤)
    (hZ : Nat.card (Subgroup.center Q) = 3) (hcard : Nat.card Q = 1080)
    (ψ6 : Q ⧸ Subgroup.center Q ≃* ↥A6Models.psl29) {σ : MulAut Q}
    (hfix : ∀ z ∈ Subgroup.center Q, σ z = z) {b : P10} (hb : b ∈ A6Models.autA6)
    (hbσ : ∀ q : Q, ((ψ6 (QuotientGroup.mk (σ q)) : ↥A6Models.psl29) : P10) =
      b * ((ψ6 (QuotientGroup.mk q) : ↥A6Models.psl29) : P10) * b⁻¹)
    {x : P10} (hx : x ∈ A6Models.psl29) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hcomm : b * x = x * b) : b ∈ A6Models.m10 := by
  by_contra hm
  obtain ⟨w, hw, hw3, hwx, hwn, hinv⟩ :=
    CFSG.RankThree.PartTwo.Sec15.Push153B.A6.exists_inv_of_not_mem_m10 hx hx3 hx1 hb hcomm hm
  set Zc := Subgroup.center (Q) with hZc
  obtain ⟨xt, hxt⟩ := ψ6.surjective ⟨x, hx⟩
  obtain ⟨q₁, rfl⟩ := QuotientGroup.mk_surjective xt
  obtain ⟨wt, hwt⟩ := ψ6.surjective ⟨w, hw⟩
  obtain ⟨q₂, rfl⟩ := QuotientGroup.mk_surjective wt
  have hψ1 : ((ψ6 (q₁ : Q ⧸ Zc) : ↥A6Models.psl29) : P10) = x := by rw [hxt]
  have hψ2 : ((ψ6 (q₂ : Q ⧸ Zc) : ↥A6Models.psl29) : P10) = w := by rw [hwt]
  have hq₁ : (q₁ : Q ⧸ Zc) ^ 3 = 1 := by
    apply ψ6.injective
    rw [map_pow, hxt, map_one]
    exact Subtype.ext (by simpa using hx3)
  have hq₂ : (q₂ : Q ⧸ Zc) ^ 3 = 1 := by
    apply ψ6.injective
    rw [map_pow, hwt, map_one]
    exact Subtype.ext (by simpa using hw3)
  have hnc := not_commute_of_lifts hperf hZ hcard ψ6 hq₁ hq₂ (by rw [hψ1]; exact hx1)
    (by rw [hψ1, hψ2]; exact hwx.symm) (by rw [hψ1, hψ2]; exact hwn)
  set c := q₁ * q₂ * q₁⁻¹ * q₂⁻¹ with hcdef
  have hc1 : c ≠ 1 := by
    intro h
    apply hnc
    rw [hcdef] at h
    calc q₁ * q₂ = q₁ * q₂ * q₁⁻¹ * q₂⁻¹ * (q₂ * q₁) := by group
      _ = q₂ * q₁ := by rw [h, one_mul]
  have hcZ : c ∈ Zc := by
    rw [← QuotientGroup.eq_one_iff]
    apply ψ6.injective
    apply Subtype.ext
    rw [hcdef, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv, QuotientGroup.mk_inv, map_mul, map_mul, map_mul, map_inv, map_inv,
      Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv,
      hψ1, hψ2, map_one, OneMemClass.coe_one]
    calc x * w * x⁻¹ * w⁻¹ = w * x * x⁻¹ * w⁻¹ := by rw [← hwx]
      _ = 1 := by group
  have hs1 : σ q₁ * q₁⁻¹ ∈ Zc := by
    have h := hbσ q₁
    rw [hψ1, hcomm, mul_inv_cancel_right, ← hψ1] at h
    have h' := ψ6.injective (Subtype.ext h)
    have h'' := QuotientGroup.eq_iff_div_mem.mp h'
    rwa [div_eq_mul_inv] at h''
  have hs2 : σ q₂ * q₂ ∈ Zc := by
    have h := hbσ q₂
    rw [hψ2, hinv] at h
    have h2 : ((ψ6 ((q₂⁻¹ : Q) : Q ⧸ Zc) : ↥A6Models.psl29) : P10) = w⁻¹ := by
      rw [QuotientGroup.mk_inv, map_inv, Subgroup.coe_inv, hψ2]
    rw [← h2] at h
    have h' := ψ6.injective (Subtype.ext h)
    have h'' := QuotientGroup.eq_iff_div_mem.mp h'
    rwa [div_eq_mul_inv, inv_inv] at h''
  set z₁ := σ q₁ * q₁⁻¹ with hz₁
  set z₂ := σ q₂ * q₂ with hz₂
  have e1 : σ q₁ = z₁ * q₁ := by rw [hz₁]; group
  have e2 : σ q₂ = z₂ * q₂⁻¹ := by rw [hz₂]; group
  have hσc : σ c = c⁻¹ := by
    have hci : c⁻¹ ∈ Zc := Zc.inv_mem hcZ
    rw [hcdef, map_mul, map_mul, map_mul, map_inv, map_inv, e1, e2,
      commutator_mul_center hs1 hs2 q₁ q₂⁻¹, ← hcdef]
    calc q₁ * q₂⁻¹ * q₁⁻¹ * q₂⁻¹⁻¹ = q₂⁻¹ * c⁻¹ * q₂ := by rw [hcdef]; group
      _ = c⁻¹ := by rw [mul_assoc, ← Subgroup.mem_center_iff.mp hci q₂]; group
  have hfixc : σ c = c := hfix c hcZ
  rw [hfixc] at hσc
  have hc2 : c * c = 1 := by
    calc c * c = c * c⁻¹ := by rw [← hσc]
      _ = 1 := mul_inv_cancel c
  have hc3 := pow_three_of_mem_center hZ hcZ
  apply hc1
  calc c = c ^ 3 * (c * c)⁻¹ := by group
    _ = 1 := by rw [hc3, hc2]; group

end ThreeA6

section Helpers

theorem eq_one_of_pow_odd_prime_of_two_power {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {g : G} (hg : g ^ p = 1) {m : ℕ} (hm : g ^ (2 ^ m) = 1) : g = 1 := by
  have h1 : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one hg
  have h2 : orderOf g ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm
  rcases (Nat.dvd_prime hp).1 h1 with h | h
  · exact orderOf_eq_one_iff.1 h
  · exfalso
    rw [h] at h2
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2)
    exact hp2 this

theorem exists_involution_of_two_elements {G : Type*} [Group G] {Q : Subgroup G}
    (hQ : ∀ b ∈ Q, ∃ m : ℕ, b ^ (2 ^ m) = 1) (hne : Q ≠ ⊥) :
    ∃ u ∈ Q, u * u = 1 ∧ u ≠ 1 := by
  obtain ⟨⟨b, hb⟩, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  obtain ⟨m, hm⟩ := hQ b hb
  have hord : orderOf b ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hb1' (orderOf_eq_one_iff.1 (by simpa using hk))
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  refine ⟨b ^ (2 ^ j), Q.pow_mem hb _, ?_, ?_⟩
  · rw [← pow_add, ← two_mul, ← pow_succ']
    exact orderOf_dvd_iff_pow_eq_one.1 (by rw [hk])
  · intro h
    have := orderOf_dvd_iff_pow_eq_one.2 h
    rw [hk] at this
    have h2 : 2 ^ (j + 1) ≤ 2 ^ j := Nat.le_of_dvd (by positivity) this
    have h3 : 2 ^ j < 2 ^ (j + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega

theorem mem_zpowers_involution {G : Type*} [Group G] {u r : G} (hu : u * u = 1)
    (hr : r ∈ Subgroup.zpowers u) : r = 1 ∨ r = u := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hr
  have h2 : u ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hu
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    have : k = 2 * (k / 2) := by omega
    rw [this, zpow_mul, h2, one_zpow]
  · right
    have : k = 2 * (k / 2) + 1 := by omega
    rw [this, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

variable {X : Type} [Group X] [Finite X]

theorem mem_map_inducedAut_iff {K : Subgroup X} {G : Type*} [Group G] (θ : MulAut ↥K →* G)
    (T : Subgroup X) {s : G} :
    s ∈ (inducedAutGroup T K).map θ ↔ ∃ (t : X) (ht : t ∈ Subgroup.normalizer (K : Set X)),
      t ∈ T ∧ θ (K.normalizerMonoidHom ⟨t, ht⟩) = s := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    obtain ⟨w, hw, hwT, rfl⟩ := mem_inducedAutGroup.1 hφ
    exact ⟨w, hw, hwT, rfl⟩
  · rintro ⟨t, ht, htT, rfl⟩
    exact ⟨_, mem_inducedAutGroup.2 ⟨t, ht, htT, rfl⟩, rfl⟩

end Helpers

section CentreSix

theorem card_center_dvd_six_of_alt6 {K : Type} [Group K]
    (hperf : commutator K = ⊤)
    (e : (K ⧸ Subgroup.center K) ≃* ↥(alternatingGroup (Fin 6))) :
    Nat.card (Subgroup.center K) ∣ 6 := by
  haveI : Group.IsPerfect K := Group.isPerfect_def.2 hperf
  have h := CFSG.HardMathSupport.Cooperstein.Coordinator.card_ker_dvd_card_hopfMultiplier
    (e.toMonoidHom.comp (QuotientGroup.mk' _)) (e.surjective.comp (QuotientGroup.mk'_surjective _))
    (CFSG.HardMathSupport.Cooperstein.Coordinator.ker_comp_mk'_center e).le
  rw [CFSG.HardMathSupport.Cooperstein.Coordinator.ker_comp_mk'_center,
    (CFSG.Alternating.Multipliers.hopfMultiplier_alternatingGroup_six).2] at h
  exact h

theorem center_cases_six {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {K : Type} [Group K] [Finite K] (hK : CFSG.IsQuasisimple K) (hO : GLAPPrimeCore p K = ⊥)
    (e : (K ⧸ Subgroup.center K) ≃* ↥(alternatingGroup (Fin 6))) :
    Subgroup.center K = ⊥ ∨ (Nat.card (Subgroup.center K) = 3 ∧ p = 3) := by
  have hodd := center_no_two_elements hp hp2 hO
  have h2 := odd_card_center_of_no_two hodd
  have h6 := card_center_dvd_six_of_alt6 (Group.isPerfect_def.1 hK.1) e
  have hcases : Nat.card (Subgroup.center K) ∈ ({1, 2, 3, 6} : Finset ℕ) := by
    have hmem : Nat.card (Subgroup.center K) ∈ Nat.divisors 6 :=
      Nat.mem_divisors.2 ⟨h6, by norm_num⟩
    have : Nat.divisors 6 = {1, 2, 3, 6} := by decide
    rw [this] at hmem; exact hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hcases
  rcases hcases with h | h | h | h
  · left; exact Subgroup.card_eq_one.1 h
  · exact absurd (by rw [h]) h2
  · right
    refine ⟨h, ?_⟩
    by_contra hp3
    have hcop : Nat.Coprime p (Nat.card (Subgroup.center K)) := by
      rw [h]
      exact (Nat.coprime_primes hp Nat.prime_three).2 hp3
    have hle : Subgroup.center K ≤ CFSG.pPrimeCore p K := le_sSup ⟨inferInstance, hcop⟩
    have hO' : CFSG.pPrimeCore p K = ⊥ := hO
    rw [hO'] at hle
    have hbot : Subgroup.center K = ⊥ := le_bot_iff.1 hle
    rw [hbot, Subgroup.card_bot] at h
    omega
  · exact absurd (by rw [h]; norm_num) h2

end CentreSix

section PerD

variable {X : Type} [Group X] [Finite X] {K : Subgroup X}
  {ε : (↥K ⧸ Subgroup.center ↥K) ≃* ↥A6Models.psl29}

theorem apd6_comm (A : APD6 K ε) {d : X} (hdN : d ∈ Subgroup.normalizer (K : Set X))
    {Sd : Subgroup X} (hSdC : Sd ≤ Subgroup.centralizer ({d} : Set X)) {t : X} (htS : t ∈ Sd)
    (ht : t ∈ Subgroup.normalizer (K : Set X)) :
    A.θ (K.normalizerMonoidHom ⟨t, ht⟩) * A.θ (K.normalizerMonoidHom ⟨d, hdN⟩) =
      A.θ (K.normalizerMonoidHom ⟨d, hdN⟩) * A.θ (K.normalizerMonoidHom ⟨t, ht⟩) := by
  have h1 : t * d = d * t := Subgroup.mem_centralizer_singleton_iff.1 (hSdC htS)
  have h2 : (⟨t, ht⟩ : ↥(Subgroup.normalizer (K : Set X))) * ⟨d, hdN⟩ =
      ⟨d, hdN⟩ * ⟨t, ht⟩ := Subtype.ext h1
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, h2]

theorem apd6_two {A : APD6 K ε} {Sd : Subgroup X} (hSd2 : ∀ t ∈ Sd, ∃ m : ℕ, t ^ (2 ^ m) = 1)
    {t : X} (htS : t ∈ Sd) (ht : t ∈ Subgroup.normalizer (K : Set X)) :
    ∃ m : ℕ, A.θ (K.normalizerMonoidHom ⟨t, ht⟩) ^ (2 ^ m) = 1 := by
  obtain ⟨m, hm⟩ := hSd2 t htS
  refine ⟨m, ?_⟩
  have h1 : (⟨t, ht⟩ : ↥(Subgroup.normalizer (K : Set X))) ^ (2 ^ m) = 1 := Subtype.ext hm
  rw [← map_pow, ← map_pow, h1, map_one, map_one]

theorem six_p3_triv (A : APD6 K ε) (hZ : Subgroup.center ↥K = ⊥) {d : X} (hd3 : d ^ 3 = 1)
    (hdN : d ∈ Subgroup.normalizer (K : Set X))
    (hσ1 : A.θ (K.normalizerMonoidHom ⟨d, hdN⟩) ≠ 1) {Sd : Subgroup X}
    (hSdC : Sd ≤ Subgroup.centralizer ({d} : Set X)) (hSd2 : ∀ t ∈ Sd, ∃ m : ℕ, t ^ (2 ^ m) = 1)
    (hSdN : Sd ≤ Subgroup.normalizer (K : Set X))
    (hSdinv : ∀ c ∈ Subgroup.centralizer ({d} : Set X), c ∈ Subgroup.normalizer (Sd : Set X)) :
    Sd ≤ Subgroup.centralizer (K : Set X) := by
  by_contra hcon
  obtain ⟨t₁, ht₁, ht₁c⟩ : ∃ t ∈ Sd, t ∉ Subgroup.centralizer (K : Set X) := by
    by_contra h
    push Not at h
    exact hcon h
  set Q : Subgroup P10 := (inducedAutGroup Sd K).map A.θ with hQ
  have hQ2 : ∀ s ∈ Q, ∃ m : ℕ, s ^ (2 ^ m) = 1 := by
    intro s hs
    obtain ⟨t, ht, htS, rfl⟩ := (mem_map_inducedAut_iff A.θ Sd).1 hs
    exact apd6_two hSd2 htS ht
  have hQne : Q ≠ ⊥ := by
    intro h
    have hmem : A.θ (K.normalizerMonoidHom ⟨t₁, hSdN ht₁⟩) ∈ Q :=
      (mem_map_inducedAut_iff A.θ Sd).2 ⟨t₁, hSdN ht₁, ht₁, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    have h2 : K.normalizerMonoidHom ⟨t₁, hSdN ht₁⟩ = 1 := A.inj (hmem.trans (map_one A.θ).symm)
    exact ht₁c ((normalizerMonoidHom_eq_one_iff (hSdN ht₁)).1 h2)
  obtain ⟨u, huQ, hu2, hu1⟩ := exists_involution_of_two_elements hQ2 hQne
  obtain ⟨t₀, ht₀, ht₀S, hut⟩ := (mem_map_inducedAut_iff A.θ Sd).1 huQ
  set σ := A.θ (K.normalizerMonoidHom ⟨d, hdN⟩) with hσdef
  have hσaut : σ ∈ A6Models.autA6 := A.mem _
  have hσ3 : σ ^ 3 = 1 := by
    have h1 : (⟨d, hdN⟩ : ↥(Subgroup.normalizer (K : Set X))) ^ 3 = 1 := Subtype.ext hd3
    rw [hσdef, ← map_pow, ← map_pow, h1, map_one, map_one]
  have hσpsl : σ ∈ A6Models.psl29 :=
    (mem_psl29_of_prime_pow Nat.prime_three (by norm_num) hσaut hσ3 hσ1).1
  have huaut : u ∈ A6Models.autA6 := hut ▸ A.mem _
  have hucomm : u * σ = σ * u := by
    rw [← hut]; exact apd6_comm A hdN hSdC ht₀S ht₀
  obtain ⟨a, haψ, haσ, hcube, hane⟩ :=
    exists_conj_involution_prod_three hσpsl hσ3 hσ1 huaut hu2 hu1 hucomm
  obtain ⟨q, hq⟩ := ε.surjective ⟨a, haψ⟩
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
  have hθk : A.θ (MulAut.conj k) = a := by rw [A.inner, hq]
  have hkd : d * (k : X) * d⁻¹ = k := by
    refine conj_comm_aux hZ hdN (A.inj ?_)
    rw [map_mul, map_mul, hθk]
    exact haσ
  have hkC : (k : X) ∈ Subgroup.centralizer ({d} : Set X) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (k : X) * d = (d * k * d⁻¹) * d := by rw [hkd]
      _ = d * k := by group
  have hkn := hSdinv _ hkC
  have hkt : (k : X) * t₀ * (k : X)⁻¹ ∈ Sd := (Subgroup.mem_normalizer_iff.1 hkn t₀).1 ht₀S
  have hktN : (k : X) * t₀ * (k : X)⁻¹ ∈ Subgroup.normalizer (K : Set X) := hSdN hkt
  have hconj : a * u * a⁻¹ = A.θ (K.normalizerMonoidHom ⟨(k : X) * t₀ * (k : X)⁻¹, hktN⟩) := by
    have e1 : (⟨(k : X) * t₀ * (k : X)⁻¹, hktN⟩ : ↥(Subgroup.normalizer (K : Set X))) =
        ⟨(k : X), Subgroup.le_normalizer k.2⟩ * ⟨t₀, ht₀⟩ * ⟨(k : X), Subgroup.le_normalizer k.2⟩⁻¹ :=
      Subtype.ext rfl
    rw [e1, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, rho_conj, hθk, hut]
  have hupart : a * u * a⁻¹ ∈ Q :=
    (mem_map_inducedAut_iff A.θ Sd).2 ⟨_, hktN, hkt, hconj.symm⟩
  have hprodQ : u * (a * u * a⁻¹) ∈ Q := Q.mul_mem huQ hupart
  obtain ⟨m, hm⟩ := hQ2 _ hprodQ
  have hprod1 := eq_one_of_pow_odd_prime_of_two_power Nat.prime_three (by norm_num) hcube hm
  apply hane
  have h1 : a * u * a⁻¹ = u⁻¹ := eq_inv_of_mul_eq_one_right hprod1
  rw [h1]
  exact inv_eq_of_mul_eq_one_left hu2

theorem six_p3_hat (A : APD6 K ε) (hperf : commutator ↥K = ⊤)
    (hZ3 : Nat.card (Subgroup.center ↥K) = 3)
    (hodd : ∀ z ∈ Subgroup.center ↥K, ∀ m : ℕ, z ^ (2 ^ m) = 1 → z = 1) {d : X} (hd3 : d ^ 3 = 1)
    (hdN : d ∈ Subgroup.normalizer (K : Set X))
    (hσ1 : A.θ (K.normalizerMonoidHom ⟨d, hdN⟩) ≠ 1) {Sd : Subgroup X}
    (hSdC : Sd ≤ Subgroup.centralizer ({d} : Set X)) (hSd2 : ∀ t ∈ Sd, ∃ m : ℕ, t ^ (2 ^ m) = 1)
    (hSdN : Sd ≤ Subgroup.normalizer (K : Set X))
    (hSdinv : ∀ c ∈ Subgroup.centralizer ({d} : Set X), c ∈ Subgroup.normalizer (Sd : Set X)) :
    Sd ≤ Subgroup.centralizer (K : Set X) := by
  by_contra hcon
  obtain ⟨t₁, ht₁, ht₁c⟩ : ∃ t ∈ Sd, t ∉ Subgroup.centralizer (K : Set X) := by
    by_contra h
    push Not at h
    exact hcon h
  set Q : Subgroup P10 := (inducedAutGroup Sd K).map A.θ with hQ
  have hQ2 : ∀ s ∈ Q, ∃ m : ℕ, s ^ (2 ^ m) = 1 := by
    intro s hs
    obtain ⟨t, ht, htS, rfl⟩ := (mem_map_inducedAut_iff A.θ Sd).1 hs
    exact apd6_two hSd2 htS ht
  have hQne : Q ≠ ⊥ := by
    intro h
    have hmem : A.θ (K.normalizerMonoidHom ⟨t₁, hSdN ht₁⟩) ∈ Q :=
      (mem_map_inducedAut_iff A.θ Sd).2 ⟨t₁, hSdN ht₁, ht₁, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    have h2 : K.normalizerMonoidHom ⟨t₁, hSdN ht₁⟩ = 1 := A.inj (hmem.trans (map_one A.θ).symm)
    exact ht₁c ((normalizerMonoidHom_eq_one_iff (hSdN ht₁)).1 h2)
  obtain ⟨u, huQ, hu2, hu1⟩ := exists_involution_of_two_elements hQ2 hQne
  obtain ⟨t₀, ht₀, ht₀S, hut⟩ := (mem_map_inducedAut_iff A.θ Sd).1 huQ
  set σ := A.θ (K.normalizerMonoidHom ⟨d, hdN⟩) with hσdef
  have hσaut : σ ∈ A6Models.autA6 := A.mem _
  have hσ3 : σ ^ 3 = 1 := by
    have h1 : (⟨d, hdN⟩ : ↥(Subgroup.normalizer (K : Set X))) ^ 3 = 1 := Subtype.ext hd3
    rw [hσdef, ← map_pow, ← map_pow, h1, map_one, map_one]
  have hσpsl : σ ∈ A6Models.psl29 :=
    (mem_psl29_of_prime_pow Nat.prime_three (by norm_num) hσaut hσ3 hσ1).1
  have huaut : u ∈ A6Models.autA6 := hut ▸ A.mem _
  have hucomm : u * σ = σ * u := by
    rw [← hut]; exact apd6_comm A hdN hSdC ht₀S ht₀
  obtain ⟨q, hq⟩ := ε.surjective ⟨σ, hσpsl⟩
  obtain ⟨k₀, rfl⟩ := QuotientGroup.mk_surjective q
  have hρd : K.normalizerMonoidHom ⟨d, hdN⟩ = MulAut.conj k₀ :=
    A.inj (by rw [A.inner, hq])
  have hdz : ∀ z ∈ Subgroup.center ↥K, d * (z : X) * d⁻¹ = z := by
    intro z hz
    have h1 : ((K.normalizerMonoidHom ⟨d, hdN⟩ z : ↥K) : X) = ((MulAut.conj k₀ z : ↥K) : X) := by
      rw [hρd]
    have h2 : d * (z : X) * d⁻¹ = (k₀ : X) * z * (k₀ : X)⁻¹ := h1
    rw [h2]
    have hz' : k₀ * z = z * k₀ := Subgroup.mem_center_iff.1 hz k₀
    calc (k₀ : X) * z * (k₀ : X)⁻¹ = ((k₀ * z : ↥K) : X) * (k₀ : X)⁻¹ := rfl
      _ = ((z * k₀ : ↥K) : X) * (k₀ : X)⁻¹ := by rw [hz']
      _ = z := by simp
  have hfix : ∀ z ∈ Subgroup.center ↥K, K.normalizerMonoidHom ⟨t₀, ht₀⟩ z = z :=
    sd_fixes_center hdz hodd hSd2 hSdinv ht₀S ht₀
  have hcard : Nat.card ↥K = 1080 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥K)
    rw [Nat.card_congr ε.toEquiv, card_psl29, hZ3] at h
    omega
  have hum : u ∈ A6Models.m10 := by
    refine mem_m10_of_fixes_center hperf hZ3 hcard ε hfix (b := u) huaut ?_ hσpsl hσ3 hσ1 hucomm
    intro q'
    rw [← hut]
    exact A.ind _ _
  exact hu1 (eq_one_of_mem_m10_involution hσpsl hσ3 hσ1 huaut hum hu2 hucomm)

theorem six_p5 (A : APD6 K ε) {d : X} (hd5 : d ^ 5 = 1) (hdN : d ∈ Subgroup.normalizer (K : Set X))
    (hσ1 : A.θ (K.normalizerMonoidHom ⟨d, hdN⟩) ≠ 1) {Sd : Subgroup X}
    (hSdC : Sd ≤ Subgroup.centralizer ({d} : Set X)) (hSd2 : ∀ t ∈ Sd, ∃ m : ℕ, t ^ (2 ^ m) = 1)
    {t : X} (htS : t ∈ Sd) (ht : t ∈ Subgroup.normalizer (K : Set X)) :
    A.θ (K.normalizerMonoidHom ⟨t, ht⟩) = 1 ∨
      (A.θ (K.normalizerMonoidHom ⟨t, ht⟩) * A.θ (K.normalizerMonoidHom ⟨t, ht⟩) = 1 ∧
        A.θ (K.normalizerMonoidHom ⟨t, ht⟩) ≠ 1 ∧
        A.θ (K.normalizerMonoidHom ⟨t, ht⟩) ∈ A6Models.pgl29 ∧
        A.θ (K.normalizerMonoidHom ⟨t, ht⟩) ∉ A6Models.psl29 ∧
        A.θ (K.normalizerMonoidHom ⟨t, ht⟩) * A.θ (K.normalizerMonoidHom ⟨d, hdN⟩) =
          A.θ (K.normalizerMonoidHom ⟨d, hdN⟩) * A.θ (K.normalizerMonoidHom ⟨t, ht⟩)) := by
  set σ := A.θ (K.normalizerMonoidHom ⟨d, hdN⟩) with hσdef
  set b := A.θ (K.normalizerMonoidHom ⟨t, ht⟩) with hbdef
  have hσaut : σ ∈ A6Models.autA6 := A.mem _
  have hσ5 : σ ^ 5 = 1 := by
    have h1 : (⟨d, hdN⟩ : ↥(Subgroup.normalizer (K : Set X))) ^ 5 = 1 := Subtype.ext hd5
    rw [hσdef, ← map_pow, ← map_pow, h1, map_one, map_one]
  have hσpsl : σ ∈ A6Models.psl29 :=
    (mem_psl29_of_prime_pow Nat.prime_five (by norm_num) hσaut hσ5 hσ1).1
  have hbaut : b ∈ A6Models.autA6 := A.mem _
  have hbσ : b * σ = σ * b := apd6_comm A hdN hSdC htS ht
  obtain ⟨m, hm⟩ := apd6_two (A := A) hSd2 htS ht
  obtain ⟨h10, hpgl, -, -⟩ := five_facts hσpsl hσ5 hσ1
  have hb10 : b ^ 10 = 1 := h10 b hbaut hbσ
  by_cases hb1 : b = 1
  · exact Or.inl hb1
  · right
    have hb2 : b * b = 1 := by
      have h5 : (b * b) ^ 5 = 1 := by
        rw [← pow_two, ← pow_mul]; exact hb10
      have hm' : (b * b) ^ (2 ^ m) = 1 := by
        rw [← pow_two, ← pow_mul, mul_comm, pow_mul, hm, one_pow]
      exact eq_one_of_pow_odd_prime_of_two_power Nat.prime_five (by norm_num) h5 hm'
    obtain ⟨hp1, hp2⟩ := hpgl b hbaut hbσ hb2 hb1
    exact ⟨hb2, hb1, hp1, hp2, hbσ⟩

theorem six_per_d {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : IsComponentOf K ⊤) (hO : GLAPPrimeCore p ↥K = ⊥) (A : APD6 K ε)
    (hZ6 : Subgroup.center ↥K = ⊥ ∨ (Nat.card (Subgroup.center ↥K) = 3 ∧ p = 3))
    {D : Subgroup X} {Sd : X → Subgroup X} (hD : SignalizerFamily p D Sd)
    (hC : SignalizerFamily.CInvariant D Sd) {d : X} (hd : d ∈ D) (hd1 : d ≠ 1) :
    Sd d ≤ Subgroup.centralizer (K : Set X) ∨
      ∃ hdN : d ∈ Subgroup.normalizer (K : Set X),
        p = 5 ∧ A.θ (K.normalizerMonoidHom ⟨d, hdN⟩) ≠ 1 := by
  have hdp : d ^ p = 1 := hD.elemAbelian.2 d hd
  have hodd := center_no_two_elements hp hp2 hO
  by_cases hdN : d ∈ Subgroup.normalizer (K : Set X)
  · by_cases hσ1 : A.θ (K.normalizerMonoidHom ⟨d, hdN⟩) = 1
    · left
      refine sd_le_centralizer hp hp2 hK hO hdp (hD.le_pCore d hd hd1) (hC d hd hd1) ?_
      intro hdN'
      exact A.inj (hσ1.trans (map_one A.θ).symm)
    · have hσaut : A.θ (K.normalizerMonoidHom ⟨d, hdN⟩) ∈ A6Models.autA6 := A.mem _
      have hσp : A.θ (K.normalizerMonoidHom ⟨d, hdN⟩) ^ p = 1 := by
        have h1 : (⟨d, hdN⟩ : ↥(Subgroup.normalizer (K : Set X))) ^ p = 1 := Subtype.ext hdp
        rw [← map_pow, ← map_pow, h1, map_one, map_one]
      obtain ⟨-, hp35⟩ := mem_psl29_of_prime_pow hp hp2 hσaut hσp hσ1
      rcases hp35 with rfl | rfl
      · left
        have hSdN : Sd d ≤ Subgroup.normalizer (K : Set X) :=
          (hD.le_pCore d hd hd1).trans
            (pCoreOf_centralizer_singleton_le_normalizer hp hp2 hK hO hdp)
        have hSdC : Sd d ≤ Subgroup.centralizer ({d} : Set X) :=
          (hD.le_pCore d hd hd1).trans (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
        have hSd2 : ∀ t ∈ Sd d, ∃ m : ℕ, t ^ (2 ^ m) = 1 := fun t ht => by
          obtain ⟨m, hm⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2
            (Subgroup.centralizer ({d} : Set X))) ⟨t, hD.le_pCore d hd hd1 ht⟩
          exact ⟨m, congrArg Subtype.val hm⟩
        rcases hZ6 with hZ | ⟨hZ3, -⟩
        · exact six_p3_triv A hZ hdp hdN hσ1 hSdC hSd2 hSdN (hC d hd hd1)
        · exact six_p3_hat A hK.2.2.1 hZ3 hodd hdp hdN hσ1 hSdC hSd2 hSdN (hC d hd hd1)
      · exact Or.inr ⟨hdN, rfl, hσ1⟩
  · left
    exact sd_le_centralizer hp hp2 hK hO hdp (hD.le_pCore d hd hd1) (hC d hd hd1)
      (fun hdN' => absurd hdN' hdN)

theorem card_induced_eq_two (A : APD6 K ε) {So : Subgroup X} {u : P10} (hu2 : u * u = 1)
    (hu1 : u ≠ 1)
    (hsub : ∀ (t : X) (ht : t ∈ Subgroup.normalizer (K : Set X)), t ∈ So →
      A.θ (K.normalizerMonoidHom ⟨t, ht⟩) = 1 ∨ A.θ (K.normalizerMonoidHom ⟨t, ht⟩) = u)
    (hmem : ∃ (t : X) (ht : t ∈ Subgroup.normalizer (K : Set X)), t ∈ So ∧
      A.θ (K.normalizerMonoidHom ⟨t, ht⟩) = u) :
    Nat.card (inducedAutGroup So K) = 2 := by
  have hmap : (inducedAutGroup So K).map A.θ = Subgroup.zpowers u := by
    apply le_antisymm
    · intro s hs
      obtain ⟨t, ht, htS, rfl⟩ := (mem_map_inducedAut_iff A.θ So).1 hs
      rcases hsub t ht htS with h | h
      · rw [h]; exact Subgroup.one_mem _
      · rw [h]; exact Subgroup.mem_zpowers u
    · rw [Subgroup.zpowers_le]
      obtain ⟨t, ht, htS, h⟩ := hmem
      exact (mem_map_inducedAut_iff A.θ So).2 ⟨t, ht, htS, h⟩
  have h1 := Subgroup.card_map_of_injective (K := inducedAutGroup So K) A.inj
  rw [hmap, Nat.card_zpowers] at h1
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1
  rw [this] at h1
  exact h1.symm

theorem psl29_sup_eq_pgl29 {u : P10} (hu_pgl : u ∈ A6Models.pgl29) (hu_psl : u ∉ A6Models.psl29) :
    A6Models.psl29 ⊔ Subgroup.zpowers u = A6Models.pgl29 := by
  have hle : A6Models.psl29 ⊔ Subgroup.zpowers u ≤ A6Models.pgl29 :=
    sup_le Out21.A6.psl29_le_pgl29 ((Subgroup.zpowers_le).2 hu_pgl)
  refine le_antisymm hle ?_
  have hlt : A6Models.psl29 < A6Models.psl29 ⊔ Subgroup.zpowers u := by
    refine lt_of_le_of_ne le_sup_left fun h => hu_psl ?_
    rw [h]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
  have hcard := Subgroup.card_lt_of_lt hlt
  have hd1 : Nat.card A6Models.psl29 ∣ Nat.card ↥(A6Models.psl29 ⊔ Subgroup.zpowers u) :=
    Subgroup.card_dvd_of_le le_sup_left
  have hd2 : Nat.card ↥(A6Models.psl29 ⊔ Subgroup.zpowers u) ∣ Nat.card A6Models.pgl29 :=
    Subgroup.card_dvd_of_le hle
  rw [card_psl29] at hd1 hcard
  rw [Out21.A6.card_pgl29] at hd2
  have heq : Nat.card ↥(A6Models.psl29 ⊔ Subgroup.zpowers u) = 720 := by
    obtain ⟨c, hc⟩ := hd2
    have hc1 : c ≤ 1 := by
      by_contra h
      push Not at h
      nlinarith
    have hc0 : c ≠ 0 := by
      rintro rfl
      omega
    have : c = 1 := by omega
    subst this
    omega
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [Out21.A6.card_pgl29, heq])).ge

theorem induced_sup_eq_pgl29 (A : APD6 K ε) {So : Subgroup X}
    (hSoN : So ≤ Subgroup.normalizer (K : Set X)) {u : P10} (hu_pgl : u ∈ A6Models.pgl29)
    (hu_psl : u ∉ A6Models.psl29)
    (hsub : ∀ (t : X) (ht : t ∈ Subgroup.normalizer (K : Set X)), t ∈ So →
      A.θ (K.normalizerMonoidHom ⟨t, ht⟩) = 1 ∨ A.θ (K.normalizerMonoidHom ⟨t, ht⟩) = u)
    (hmem : ∃ (t : X) (ht : t ∈ Subgroup.normalizer (K : Set X)), t ∈ So ∧
      A.θ (K.normalizerMonoidHom ⟨t, ht⟩) = u) :
    (inducedAutGroup (K ⊔ So) K).map A.θ = A6Models.pgl29 := by
  have hθK : ∀ k : ↥K,
      A.θ (K.normalizerMonoidHom ⟨(k : X), Subgroup.le_normalizer k.2⟩) =
        ((ε (QuotientGroup.mk k) : ↥A6Models.psl29) : P10) := fun k => by
    rw [rho_conj, A.inner]
  apply le_antisymm
  · intro s hs
    obtain ⟨w, hw, hwKS, rfl⟩ := (mem_map_inducedAut_iff A.θ (K ⊔ So)).1 hs
    let Hp : Subgroup X := (A6Models.pgl29.comap (A.θ.comp K.normalizerMonoidHom)).map
      (Subgroup.normalizer (K : Set X)).subtype
    have hKp : K ≤ Hp := by
      intro k hk
      refine ⟨⟨k, Subgroup.le_normalizer hk⟩, ?_, rfl⟩
      show A.θ (K.normalizerMonoidHom ⟨(⟨k, hk⟩ : ↥K), Subgroup.le_normalizer hk⟩) ∈
        A6Models.pgl29
      rw [hθK ⟨k, hk⟩]
      exact Out21.A6.psl29_le_pgl29 (ε _).2
    have hSp : So ≤ Hp := by
      intro t htS
      refine ⟨⟨t, hSoN htS⟩, ?_, rfl⟩
      show A.θ (K.normalizerMonoidHom ⟨t, hSoN htS⟩) ∈ A6Models.pgl29
      rcases hsub t (hSoN htS) htS with h | h
      · rw [h]; exact A6Models.pgl29.one_mem
      · rw [h]; exact hu_pgl
    obtain ⟨n, hn, hnw⟩ := sup_le hKp hSp hwKS
    have hnw' : n = ⟨w, hw⟩ := Subtype.ext hnw
    subst hnw'
    exact hn
  · rw [← psl29_sup_eq_pgl29 hu_pgl hu_psl]
    apply sup_le
    · intro y hy
      obtain ⟨q, hq⟩ := ε.surjective ⟨y, hy⟩
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
      refine (mem_map_inducedAut_iff A.θ (K ⊔ So)).2
        ⟨(k : X), Subgroup.le_normalizer k.2, Subgroup.mem_sup_left k.2, ?_⟩
      rw [hθK, hq]
    · rw [Subgroup.zpowers_le]
      obtain ⟨t, ht, htS, h⟩ := hmem
      exact (mem_map_inducedAut_iff A.θ (K ⊔ So)).2 ⟨t, ht, Subgroup.mem_sup_right htS, h⟩

end PerD

section TwoSix

variable {X : Type} [Group X] [Finite X]

theorem input19_21_2_six {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {K : Subgroup X} (hK : IsComponentOf K ⊤) (hO : GLAPPrimeCore p ↥K = ⊥)
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(alternatingGroup (Fin 6)))
    {D : Subgroup X} {Sd : X → Subgroup X} (hD : SignalizerFamily p D Sd)
    (hC : SignalizerFamily.CInvariant D Sd) {So : Subgroup X}
    (hSo : So ≤ pCoreOf 2 (sigmaFam D Sd)) :
    So ≤ Subgroup.centralizer (K : Set X) ∨
      (p = 5 ∧ Nat.card (inducedAutGroup So K) = 2 ∧
        Nonempty (↥(inducedAutGroup (K ⊔ So) K) ≃* ↥CFSG.QuasithinUnique.A6Models.pgl29)) := by
  classical
  have hKq := isQuasisimple_of_comp hK
  have hZ6 := center_cases_six hp hp2 hKq hO e
  obtain ⟨ε, -⟩ : ∃ ε : (↥K ⧸ Subgroup.center ↥K) ≃* ↥A6Models.psl29, True := by
    obtain ⟨ψ, -⟩ := DoubleA3.exists_psl_equiv
    exact ⟨e.trans ψ.symm, trivial⟩
  obtain ⟨A⟩ := exists_apd6 hK.2.2.1 ε
  have hDp : ∀ d ∈ D, d ^ p = 1 := hD.elemAbelian.2
  have hDc : ∀ d ∈ D, ∀ d' ∈ D, d * d' = d' * d := fun d hd d' hd' =>
    congrArg Subtype.val (hD.elemAbelian.1.is_comm.comm (⟨d, hd⟩ : D) ⟨d', hd'⟩)
  have hSdN : ∀ d ∈ D, d ≠ 1 → Sd d ≤ Subgroup.normalizer (K : Set X) := fun d hd hd1 =>
    (hD.le_pCore d hd hd1).trans
      (pCoreOf_centralizer_singleton_le_normalizer hp hp2 hK hO (hDp d hd))
  have hSdC : ∀ d ∈ D, d ≠ 1 → Sd d ≤ Subgroup.centralizer ({d} : Set X) := fun d hd hd1 =>
    (hD.le_pCore d hd hd1).trans (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
  have hSd2 : ∀ d ∈ D, d ≠ 1 → ∀ t ∈ Sd d, ∃ m : ℕ, t ^ (2 ^ m) = 1 := fun d hd hd1 t ht => by
    obtain ⟨m, hm⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2
      (Subgroup.centralizer ({d} : Set X))) ⟨t, hD.le_pCore d hd hd1 ht⟩
    exact ⟨m, congrArg Subtype.val hm⟩
  have hSN : sigmaFam D Sd ≤ Subgroup.normalizer (K : Set X) :=
    sigmaFam_le_normalizer hp hp2 hK hO hD
  have hSoS : So ≤ sigmaFam D Sd := hSo.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
  have hSoN : So ≤ Subgroup.normalizer (K : Set X) := hSoS.trans hSN
  by_cases hex : ∃ d ∈ D, d ≠ 1 ∧ ¬ Sd d ≤ Subgroup.centralizer (K : Set X)
  swap
  · left
    push Not at hex
    refine hSoS.trans ?_
    exact iSup_le fun d => iSup_le fun hd => iSup_le fun hd1 => hex d hd hd1
  obtain ⟨d₁, hd₁D, hd₁1, hd₁nc⟩ := hex
  rcases six_per_d hp hp2 hK hO A hZ6 hD hC hd₁D hd₁1 with h | ⟨hdN₁, hp5, hσ₁1⟩
  · exact absurd h hd₁nc
  subst hp5
  obtain ⟨t₁, ht₁S, ht₁c⟩ : ∃ t ∈ Sd d₁, t ∉ Subgroup.centralizer (K : Set X) := by
    by_contra h
    push Not at h
    exact hd₁nc h
  have hσ₁aut : A.θ (K.normalizerMonoidHom ⟨d₁, hdN₁⟩) ∈ A6Models.autA6 := A.mem _
  have hσ₁5 : A.θ (K.normalizerMonoidHom ⟨d₁, hdN₁⟩) ^ 5 = 1 := by
    have h1 : (⟨d₁, hdN₁⟩ : ↥(Subgroup.normalizer (K : Set X))) ^ 5 = 1 := Subtype.ext (hDp d₁ hd₁D)
    rw [← map_pow, ← map_pow, h1, map_one, map_one]
  have hσ₁psl : A.θ (K.normalizerMonoidHom ⟨d₁, hdN₁⟩) ∈ A6Models.psl29 :=
    (mem_psl29_of_prime_pow Nat.prime_five (by norm_num) hσ₁aut hσ₁5 hσ₁1).1
  have hb₁ := six_p5 A (hDp d₁ hd₁D) hdN₁ hσ₁1 (hSdC d₁ hd₁D hd₁1) (hSd2 d₁ hd₁D hd₁1) ht₁S
    (hSdN d₁ hd₁D hd₁1 ht₁S)
  have hb₁ne : A.θ (K.normalizerMonoidHom ⟨t₁, hSdN d₁ hd₁D hd₁1 ht₁S⟩) ≠ 1 := by
    intro h
    apply ht₁c
    exact (normalizerMonoidHom_eq_one_iff _).1 (A.inj (h.trans (map_one A.θ).symm))
  obtain ⟨hu2, hu1, hu_pgl, hu_psl, hu_comm⟩ := hb₁.resolve_left hb₁ne
  obtain ⟨u, hu⟩ : ∃ u : P10,
      u = A.θ (K.normalizerMonoidHom ⟨t₁, hSdN d₁ hd₁D hd₁1 ht₁S⟩) := ⟨_, rfl⟩
  rw [← hu] at hu2 hu1 hu_pgl hu_psl hu_comm
  have huaut : u ∈ A6Models.autA6 := hu ▸ A.mem _
  have hsub : ∀ d ∈ D, d ≠ 1 → ∀ (t : X) (ht : t ∈ Subgroup.normalizer (K : Set X)), t ∈ Sd d →
      A.θ (K.normalizerMonoidHom ⟨t, ht⟩) = 1 ∨ A.θ (K.normalizerMonoidHom ⟨t, ht⟩) = u := by
    intro d hd hd1 t ht htS
    rcases six_per_d hp hp2 hK hO A hZ6 hD hC hd hd1 with h | ⟨hdN, -, hσ1⟩
    · left
      have : K.normalizerMonoidHom ⟨t, ht⟩ = 1 := (normalizerMonoidHom_eq_one_iff ht).2 (h htS)
      rw [this, map_one]
    · rcases six_p5 A (hDp d hd) hdN hσ1 (hSdC d hd hd1) (hSd2 d hd hd1) htS ht with
        h | ⟨hb2, hb1, hbpgl, hbpsl, hbσ⟩
      · exact Or.inl h
      · right
        have hσaut : A.θ (K.normalizerMonoidHom ⟨d, hdN⟩) ∈ A6Models.autA6 := A.mem _
        have hσ5 : A.θ (K.normalizerMonoidHom ⟨d, hdN⟩) ^ 5 = 1 := by
          have h1 : (⟨d, hdN⟩ : ↥(Subgroup.normalizer (K : Set X))) ^ 5 = 1 :=
            Subtype.ext (hDp d hd)
          rw [← map_pow, ← map_pow, h1, map_one, map_one]
        have hσpsl : A.θ (K.normalizerMonoidHom ⟨d, hdN⟩) ∈ A6Models.psl29 :=
          (mem_psl29_of_prime_pow Nat.prime_five (by norm_num) hσaut hσ5 hσ1).1
        have hcommσ : A.θ (K.normalizerMonoidHom ⟨d₁, hdN₁⟩) *
            A.θ (K.normalizerMonoidHom ⟨d, hdN⟩) =
            A.θ (K.normalizerMonoidHom ⟨d, hdN⟩) * A.θ (K.normalizerMonoidHom ⟨d₁, hdN₁⟩) := by
          have h2 : (⟨d₁, hdN₁⟩ : ↥(Subgroup.normalizer (K : Set X))) * ⟨d, hdN⟩ =
              ⟨d, hdN⟩ * ⟨d₁, hdN₁⟩ := Subtype.ext (hDc d₁ hd₁D d hd)
          rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, h2]
        obtain ⟨-, -, -, hgen⟩ := five_facts hσpsl hσ5 hσ1
        obtain ⟨j, hj⟩ := hgen _ hσ₁psl hσ₁5 hσ₁1 hcommσ
        have hbaut : A.θ (K.normalizerMonoidHom ⟨t, ht⟩) ∈ A6Models.autA6 := A.mem _
        have hbσ₁ : A.θ (K.normalizerMonoidHom ⟨t, ht⟩) *
            A.θ (K.normalizerMonoidHom ⟨d₁, hdN₁⟩) =
            A.θ (K.normalizerMonoidHom ⟨d₁, hdN₁⟩) * A.θ (K.normalizerMonoidHom ⟨t, ht⟩) := by
          rw [hj]
          exact (Commute.pow_right (show Commute _ _ from hbσ) j).eq
        obtain ⟨-, -, huniq, -⟩ := five_facts hσ₁psl hσ₁5 hσ₁1
        exact huniq _ hbaut u huaut hbσ₁ hu_comm hb2 hu2 hb1 hu1
  have hsubS : ∀ (t : X) (ht : t ∈ Subgroup.normalizer (K : Set X)), t ∈ sigmaFam D Sd →
      A.θ (K.normalizerMonoidHom ⟨t, ht⟩) = 1 ∨ A.θ (K.normalizerMonoidHom ⟨t, ht⟩) = u := by
    let Ψ6 : ↥(Subgroup.normalizer (K : Set X)) →* P10 := A.θ.comp K.normalizerMonoidHom
    have hle : sigmaFam D Sd ≤
        ((Subgroup.zpowers u).comap Ψ6).map (Subgroup.normalizer (K : Set X)).subtype := by
      refine iSup_le fun d => iSup_le fun hd => iSup_le fun hd1 => ?_
      intro t ht
      refine ⟨⟨t, hSdN d hd hd1 ht⟩, ?_, rfl⟩
      show A.θ (K.normalizerMonoidHom ⟨t, hSdN d hd hd1 ht⟩) ∈ Subgroup.zpowers u
      rcases hsub d hd hd1 t (hSdN d hd hd1 ht) ht with h | h
      · rw [h]; exact Subgroup.one_mem _
      · rw [h]; exact Subgroup.mem_zpowers u
    intro t ht htS
    obtain ⟨n, hn, hnt⟩ := hle htS
    have hnt' : n = ⟨t, ht⟩ := Subtype.ext hnt
    subst hnt'
    exact mem_zpowers_involution hu2 hn
  have hsubSo : ∀ (t : X) (ht : t ∈ Subgroup.normalizer (K : Set X)), t ∈ So →
      A.θ (K.normalizerMonoidHom ⟨t, ht⟩) = 1 ∨ A.θ (K.normalizerMonoidHom ⟨t, ht⟩) = u :=
    fun t ht htSo => hsubS t ht (hSoS htSo)
  by_cases hall : ∀ (t : X) (ht : t ∈ Subgroup.normalizer (K : Set X)), t ∈ So →
      A.θ (K.normalizerMonoidHom ⟨t, ht⟩) = 1
  · left
    intro t htSo
    exact (normalizerMonoidHom_eq_one_iff (hSoN htSo)).1
      (A.inj ((hall t (hSoN htSo) htSo).trans (map_one A.θ).symm))
  · right
    push Not at hall
    obtain ⟨t', ht', ht'S, ht'ne⟩ := hall
    have hmem : ∃ (t : X) (ht : t ∈ Subgroup.normalizer (K : Set X)), t ∈ So ∧
        A.θ (K.normalizerMonoidHom ⟨t, ht⟩) = u :=
      ⟨t', ht', ht'S, (hsubSo t' ht' ht'S).resolve_left ht'ne⟩
    refine ⟨rfl, card_induced_eq_two A hu2 hu1 hsubSo hmem, ?_⟩
    have hmap := induced_sup_eq_pgl29 A hSoN hu_pgl hu_psl hsubSo hmem
    exact ⟨(Subgroup.equivMapOfInjective _ A.θ A.inj).trans (MulEquiv.subgroupCongr hmap)⟩

end TwoSix

end CFSG.LocalAnalysis.GLTheoremB.Prop95I1921
