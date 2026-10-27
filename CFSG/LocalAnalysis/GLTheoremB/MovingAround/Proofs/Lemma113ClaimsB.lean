module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma113ClaimsCtx
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma113e
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec10Closed4
public import CFSG.Sporadic.Schreier.J4SNoCompCover
public import Certificates.Kernel.J4Count.Fix11
public import Certificates.Kernel.J4Count.Cent11Base

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf barAut)
open scoped MatrixGroups Pointwise

namespace Lemma113Claims.B

variable {G : Type} [Group G] [Finite G]

theorem isPGroup_of_isElemAbelian' {p : ℕ} [Fact p.Prime] {F : Subgroup G}
    (hF : IsElemAbelian p F) : IsPGroup p F := by
  rw [IsPGroup.iff_orderOf]
  intro g
  have hg : (g : G) ^ p = 1 := hF.2 (g : G) g.2
  have hgp : g ^ p = 1 := Subtype.ext (by simpa using hg)
  rcases (Nat.dvd_prime (Fact.out : p.Prime)).1 (orderOf_dvd_of_pow_eq_one hgp) with h1 | h1
  · exact ⟨0, by simp [h1]⟩
  · exact ⟨1, by simp [h1]⟩

variable {E A : Subgroup G} {e : G} {K Q : Subgroup G}

theorem P_le (c : Ctx E A e K Q) : (Q ⊓ K : Subgroup G) ⊔ centBar 3 Q K ≤ Q :=
  sup_le inf_le_left c.centBar_le

theorem P_conj (c : Ctx E A e K Q) {q : G} (hq : q ∈ Q) {n : G}
    (hn : n ∈ (Q ⊓ K : Subgroup G) ⊔ centBar 3 Q K) :
    q * n * q⁻¹ ∈ (Q ⊓ K : Subgroup G) ⊔ centBar 3 Q K :=
  (Subgroup.mem_normalizer_iff.1 (Lemma113d.le_normalizer_sup_centBar c.hQK hq) n).1 hn

theorem mem_E_of_mem_P (c : Ctx E A e K Q) {y : G}
    (hy : y ∈ (Q ⊓ K : Subgroup G) ⊔ centBar 3 Q K) (hy3 : y ^ 3 = 1) : y ∈ E := by
  rw [c.hEeq]
  exact Lemma113d.mem_sup_zpowers_of_pow_three c.hQ c.hQ1 c.hXN c.hKX c.hKI c.hcyc c.hKe c.he3
    c.he1 c.heQ hy hy3

theorem mem_Z_of_mem_P (c : Ctx E A e K Q) {x : G} (hxA : x ∈ A)
    (hxP : x ∈ (Q ⊓ K : Subgroup G) ⊔ centBar 3 Q K) : x ∈ E ⊓ A :=
  ⟨mem_E_of_mem_P c hxP (c.hAel.2 x hxA), hxA⟩

theorem exists_t (c : Ctx E A e K Q) : ∃ t ∈ A, t ∉ (Q ⊓ K : Subgroup G) ⊔ centBar 3 Q K :=
  Lemma113d.exists_mem_not_mem_sup c.hQ c.hQ1 c.hXN c.hKX c.hKI c.hcyc c.hKe c.he3 c.he1 c.heQ
    c.hAmax c.hAel (by rw [c.hAcard]; norm_num)

theorem sup_eq (c : Ctx E A e K Q) {s : G} (hsQ : s ∈ Q) (hs3 : s ^ 3 = 1)
    (hsP : s ∉ (Q ⊓ K : Subgroup G) ⊔ centBar 3 Q K) :
    ((Q ⊓ K : Subgroup G) ⊔ centBar 3 Q K) ⊔ Subgroup.zpowers s = Q := by
  obtain ⟨e0⟩ := c.hKI
  exact Lemma113d.sup_zpowers_eq_top c.hQK (Lemma113d.card_le_81_mul_centBar e0 c.hQp c.hQK)
    c.card_Q0 (fun a ha u hu => (c.comm_centBar_Q0 hu ha).symm) c.Q0_inf_centBar hsQ hs3 hsP

theorem exists_decomp (c : Ctx E A e K Q) {s : G} (hsQ : s ∈ Q) (hs3 : s ^ 3 = 1)
    (hsP : s ∉ (Q ⊓ K : Subgroup G) ⊔ centBar 3 Q K) {y : G} (hy : y ∈ Q) :
    ∃ n ∈ (Q ⊓ K : Subgroup G) ⊔ centBar 3 Q K, ∃ k : ℤ, y = n * s ^ k :=
  Lemma113d.exists_eq_mul_zpow_of_sup_eq (P_le c) (fun _ hq _ hn => P_conj c hq hn) hsQ
    (sup_eq c hsQ hs3 hsP) hy

theorem conj_mem_Ubar (c : Ctx E A e K Q) {q : G} (hq : q ∈ Q) {u : MulAut (barOf 3 K)}
    (hu : u ∈ Lemma113d.Ubar c.hQK) :
    Lemma113d.rhoQ c.hQK ⟨q, hq⟩ * u * (Lemma113d.rhoQ c.hQK ⟨q, hq⟩)⁻¹ ∈
      Lemma113d.Ubar c.hQK := by
  obtain ⟨d, rfl⟩ := hu
  have hd : ((d : ↥((Q ⊓ K : Subgroup G).subgroupOf Q)) : G) ∈ (Q ⊓ K : Subgroup G) :=
    Subgroup.mem_subgroupOf.1 d.2
  have hd' := (c.Q0_normal_in_Q hq).1 hd
  refine ⟨⟨⟨q * d * q⁻¹, hd'.1⟩, Subgroup.mem_subgroupOf.2 hd'⟩, ?_⟩
  simp only [MonoidHom.comp_apply, Subgroup.subtype_apply]
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1

theorem card_centralizer_le (c : Ctx E A e K Q) {s : G} (hsQ : s ∈ Q) (hs3 : s ^ 3 = 1)
    (hsP : s ∉ (Q ⊓ K : Subgroup G) ⊔ centBar 3 Q K) :
    Nat.card ↥((Q ⊓ K : Subgroup G) ⊓ Subgroup.centralizer ({s} : Set G)) ≤ 3 := by
  classical
  obtain ⟨e0⟩ := c.hKI
  have hU := Lemma113d.Ubar_elemAbelian c.hQ c.hQ1 c.hXN c.hKX c.hKI
  have hU27 := Lemma113d.Ubar_card c.hQ c.hQ1 c.hXN c.hKX c.hKI
  have hσN : Lemma113d.rhoQ c.hQK ⟨s, hsQ⟩ ∈
      Subgroup.normalizer ((Lemma113d.Ubar c.hQK : Subgroup (MulAut (barOf 3 K))) :
        Set (MulAut (barOf 3 K))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · intro hu
      exact conj_mem_Ubar c hsQ hu
    · intro hu
      have h1 := conj_mem_Ubar c (Q.inv_mem hsQ) hu
      have h2 : Lemma113d.rhoQ c.hQK ⟨s⁻¹, Q.inv_mem hsQ⟩ =
          (Lemma113d.rhoQ c.hQK ⟨s, hsQ⟩)⁻¹ := by
        rw [← map_inv]
        rfl
      rw [h2, inv_inv] at h1
      simpa [mul_assoc] using h1
  have hσ3 : (Lemma113d.rhoQ c.hQK ⟨s, hsQ⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨s, hsQ⟩ : ↥Q) ^ 3 = 1 := Subtype.ext (by simpa using hs3)
    rw [this, map_one]
  have hσI : Lemma113d.rhoQ c.hQK ⟨s, hsQ⟩ ∉
      (MulAut.conj : barOf 3 K →* MulAut (barOf 3 K)).range := fun h =>
    hsP (Lemma113d.mem_sup_of_rho_inner e0 c.hQp c.hQK hU27 ⟨s, hsQ⟩ h)
  have key := hC113 (barOf 3 K) e0 (Lemma113d.rhoQ c.hQK ⟨s, hsQ⟩) (Lemma113d.Ubar c.hQK) hσN
    hσ3 hσI (Lemma113d.Ubar_le_inner c.hQK) hU hU27
  let f : ↥((Q ⊓ K : Subgroup G) ⊓ Subgroup.centralizer ({s} : Set G)) →
      ↥(Lemma113d.Ubar c.hQK ⊓
        Subgroup.centralizer ({Lemma113d.rhoQ c.hQK ⟨s, hsQ⟩} : Set (MulAut (barOf 3 K)))) :=
    fun d => ⟨Lemma113d.rhoQ c.hQK ⟨d, d.2.1.1⟩, Subgroup.mem_inf.2
      ⟨⟨⟨⟨d, d.2.1.1⟩, Subgroup.mem_subgroupOf.2 d.2.1⟩, rfl⟩, by
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        rw [Set.mem_singleton_iff.1 hx, ← map_mul, ← map_mul]
        congr 1
        apply Subtype.ext
        exact Subgroup.mem_centralizer_iff.1 d.2.2 s (Set.mem_singleton s)⟩⟩
  have hf : Function.Injective f := by
    intro d₁ d₂ h
    have h1 : Lemma113d.rhoQ c.hQK ⟨d₁, d₁.2.1.1⟩ = Lemma113d.rhoQ c.hQK ⟨d₂, d₂.2.1.1⟩ :=
      congrArg Subtype.val h
    have h2 : Lemma113d.rhoQ c.hQK ((⟨d₁, d₁.2.1.1⟩ : ↥Q)⁻¹ * ⟨d₂, d₂.2.1.1⟩) = 1 := by
      rw [map_mul, map_inv, h1, inv_mul_cancel]
    have h3 := (Lemma113d.rhoQ_eq_one_iff c.hQK _).1 h2
    have h4 : ((d₁ : G))⁻¹ * d₂ ∈ (Q ⊓ K : Subgroup G) ⊓ centBar 3 Q K :=
      ⟨(Q ⊓ K : Subgroup G).mul_mem ((Q ⊓ K : Subgroup G).inv_mem d₁.2.1) d₂.2.1, h3⟩
    rw [c.Q0_inf_centBar, Subgroup.mem_bot] at h4
    exact Subtype.ext (inv_mul_eq_one.1 h4)
  exact (Nat.card_le_card_of_injective f hf).trans key

@[expose] noncomputable def phiH (c : Ctx E A e K Q) {s : G} (hsQ : s ∈ Q) :
    ↥(Q ⊓ K : Subgroup G) →* ↥(Q ⊓ K : Subgroup G) where
  toFun b := ⟨(b : G) * (s * b * s⁻¹)⁻¹,
    (Q ⊓ K : Subgroup G).mul_mem b.2 ((Q ⊓ K : Subgroup G).inv_mem ((c.Q0_normal_in_Q hsQ).1 b.2))⟩
  map_one' := by
    apply Subtype.ext
    show ((1 : ↥(Q ⊓ K : Subgroup G)) : G) * (s * ((1 : ↥(Q ⊓ K : Subgroup G)) : G) * s⁻¹)⁻¹ = 1
    simp
  map_mul' := by
    intro x y
    apply Subtype.ext
    show ((x : G) * y) * (s * ((x : G) * y) * s⁻¹)⁻¹ =
      ((x : G) * (s * x * s⁻¹)⁻¹) * ((y : G) * (s * y * s⁻¹)⁻¹)
    have hx' := (c.Q0_normal_in_Q hsQ).1 x.2
    have hy' := (c.Q0_normal_in_Q hsQ).1 y.2
    have hc : (s * (x : G) * s⁻¹)⁻¹ * ((y : G) * (s * y * s⁻¹)⁻¹) =
        ((y : G) * (s * y * s⁻¹)⁻¹) * (s * (x : G) * s⁻¹)⁻¹ :=
      elemAbelian_comm c.Q0_elemAbelian ((Q ⊓ K : Subgroup G).inv_mem hx')
        ((Q ⊓ K : Subgroup G).mul_mem y.2 ((Q ⊓ K : Subgroup G).inv_mem hy'))
    calc ((x : G) * y) * (s * ((x : G) * y) * s⁻¹)⁻¹
        = (x : G) * (((y : G) * (s * y * s⁻¹)⁻¹) * (s * (x : G) * s⁻¹)⁻¹) := by group
      _ = (x : G) * ((s * (x : G) * s⁻¹)⁻¹ * ((y : G) * (s * y * s⁻¹)⁻¹)) := by rw [hc]
      _ = ((x : G) * (s * x * s⁻¹)⁻¹) * ((y : G) * (s * y * s⁻¹)⁻¹) := by group

theorem phiH_apply (c : Ctx E A e K Q) {s : G} (hsQ : s ∈ Q) (b : ↥(Q ⊓ K : Subgroup G)) :
    ((phiH c hsQ b : ↥(Q ⊓ K : Subgroup G)) : G) = (b : G) * (s * b * s⁻¹)⁻¹ := rfl

theorem phiH_phiH (c : Ctx E A e K Q) {s : G} (hsQ : s ∈ Q) (b : ↥(Q ⊓ K : Subgroup G)) :
    ((phiH c hsQ (phiH c hsQ b) : ↥(Q ⊓ K : Subgroup G)) : G) =
      (b : G) * (s * b * s⁻¹) * (s ^ 2 * b * (s ^ 2)⁻¹) := by
  rw [phiH_apply, phiH_apply]
  have hxQ : s * (b : G) * s⁻¹ ∈ (Q ⊓ K : Subgroup G) := (c.Q0_normal_in_Q hsQ).1 b.2
  have hyQ : s * (s * (b : G) * s⁻¹) * s⁻¹ ∈ (Q ⊓ K : Subgroup G) :=
    (c.Q0_normal_in_Q hsQ).1 hxQ
  have hy : s ^ 2 * (b : G) * (s ^ 2)⁻¹ = s * (s * (b : G) * s⁻¹) * s⁻¹ := by
    simp only [pow_two]; group
  rw [hy]
  generalize hx : s * (b : G) * s⁻¹ = x at hxQ hyQ ⊢
  have e1 : s * ((b : G) * x⁻¹) * s⁻¹ = x * (s * x * s⁻¹)⁻¹ := by rw [← hx]; group
  rw [e1]
  generalize s * x * s⁻¹ = y at hyQ ⊢
  have hx3 : x ^ 3 = 1 := c.Q0_elemAbelian.2 x hxQ
  have hxy : x⁻¹ * y = y * x⁻¹ :=
    elemAbelian_comm c.Q0_elemAbelian ((Q ⊓ K : Subgroup G).inv_mem hxQ) hyQ
  have hxy' : y * x = x * y := elemAbelian_comm c.Q0_elemAbelian hyQ hxQ
  have hxx : x⁻¹ * x⁻¹ = x := by
    calc x⁻¹ * x⁻¹ = x⁻¹ * x⁻¹ * x ^ 3 := by rw [hx3, mul_one]
      _ = x := by group
  calc (b : G) * x⁻¹ * (x * y⁻¹)⁻¹ = (b : G) * (x⁻¹ * y) * x⁻¹ := by group
    _ = (b : G) * (y * x⁻¹) * x⁻¹ := by rw [hxy]
    _ = (b : G) * y * (x⁻¹ * x⁻¹) := by group
    _ = (b : G) * (y * x) := by rw [hxx, mul_assoc]
    _ = (b : G) * x * y := by rw [hxy', mul_assoc]

theorem phiH_cube (c : Ctx E A e K Q) {s : G} (hsQ : s ∈ Q) (hs3 : s ^ 3 = 1)
    (b : ↥(Q ⊓ K : Subgroup G)) : phiH c hsQ (phiH c hsQ (phiH c hsQ b)) = 1 := by
  apply Subtype.ext
  rw [phiH_phiH, phiH_apply]
  show (b : G) * (s * b * s⁻¹)⁻¹ * (s * ((b : G) * (s * b * s⁻¹)⁻¹) * s⁻¹) *
      (s ^ 2 * ((b : G) * (s * b * s⁻¹)⁻¹) * (s ^ 2)⁻¹) = 1
  calc (b : G) * (s * b * s⁻¹)⁻¹ * (s * ((b : G) * (s * b * s⁻¹)⁻¹) * s⁻¹) *
        (s ^ 2 * ((b : G) * (s * b * s⁻¹)⁻¹) * (s ^ 2)⁻¹)
      = (b : G) * (s ^ 3 * (b : G)⁻¹ * (s ^ 3)⁻¹) := by simp only [pow_two, pow_three]; group
    _ = 1 := by rw [hs3]; group

theorem exists_phiH_eq (c : Ctx E A e K Q) {s : G} (hsQ : s ∈ Q) (hs3 : s ^ 3 = 1)
    (hsP : s ∉ (Q ⊓ K : Subgroup G) ⊔ centBar 3 Q K) {a : G} (ha : a ∈ (Q ⊓ K : Subgroup G))
    (hN : a * (s * a * s⁻¹) * (s ^ 2 * a * (s ^ 2)⁻¹) = 1) :
    ∃ b ∈ (Q ⊓ K : Subgroup G), a = b * (s * b * s⁻¹)⁻¹ := by
  classical
  have hker : Nat.card ↥(phiH c hsQ).ker ≤ 3 := by
    refine le_trans ?_ (card_centralizer_le c hsQ hs3 hsP)
    let f : ↥(phiH c hsQ).ker → ↥((Q ⊓ K : Subgroup G) ⊓ Subgroup.centralizer ({s} : Set G)) :=
      fun b => ⟨((b : ↥(Q ⊓ K : Subgroup G)) : G), Subgroup.mem_inf.2 ⟨(b : ↥(Q ⊓ K : Subgroup G)).2, by
        have hb1 : (((b : ↥(Q ⊓ K : Subgroup G)) : G)) *
            (s * ((b : ↥(Q ⊓ K : Subgroup G)) : G) * s⁻¹)⁻¹ = 1 :=
          congrArg Subtype.val (MonoidHom.mem_ker.1 b.2)
        have hb2 := mul_inv_eq_one.1 hb1
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.1 hh]
        calc s * ((b : ↥(Q ⊓ K : Subgroup G)) : G) =
            (s * ((b : ↥(Q ⊓ K : Subgroup G)) : G) * s⁻¹) * s := by group
          _ = ((b : ↥(Q ⊓ K : Subgroup G)) : G) * s := by rw [← hb2]⟩⟩
    refine Nat.card_le_card_of_injective f (fun x y h => ?_)
    have h' := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')
  have hcardQ0 : Nat.card ↥(Q ⊓ K : Subgroup G) = 27 := c.card_Q0
  have hsplit := CFSG.RankThree.PartTwo.KFacts.card_eq_card_ker_mul_card_range (phiH c hsQ)
  rw [hcardQ0] at hsplit
  have hrange : 9 ≤ Nat.card ↥(phiH c hsQ).range := by
    by_contra hlt
    push Not at hlt
    have h8 : Nat.card ↥(phiH c hsQ).range ≤ 8 := by omega
    have := Nat.mul_le_mul hker h8
    omega
  have hle : (phiH c hsQ).range ≤ ((phiH c hsQ).comp (phiH c hsQ)).ker := by
    rintro _ ⟨b, rfl⟩
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact phiH_cube c hsQ hs3 b
  have hne : ((phiH c hsQ).comp (phiH c hsQ)).ker ≠ ⊤ := by
    intro htop
    have hrk : (phiH c hsQ).range ≤ (phiH c hsQ).ker := by
      rintro _ ⟨b, rfl⟩
      have hb : b ∈ ((phiH c hsQ).comp (phiH c hsQ)).ker := by rw [htop]; trivial
      exact hb
    have := Subgroup.card_le_of_le hrk
    omega
  have hkle : Nat.card ↥((phiH c hsQ).comp (phiH c hsQ)).ker ≤ 9 := by
    have hdvd : Nat.card ↥((phiH c hsQ).comp (phiH c hsQ)).ker ∣ 3 ^ 3 := by
      rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hcardQ0]
      exact Subgroup.card_subgroup_dvd_card _
    obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    have hne27 : Nat.card ↥((phiH c hsQ).comp (phiH c hsQ)).ker ≠ 27 := by
      intro h27
      apply hne
      apply Subgroup.eq_top_of_card_eq
      rw [h27, hcardQ0]
    rw [hjeq] at hne27 ⊢
    interval_cases j <;> simp_all
  have heq : (phiH c hsQ).range = ((phiH c hsQ).comp (phiH c hsQ)).ker :=
    Subgroup.eq_of_le_of_card_ge hle (by omega)
  have ha' : (⟨a, ha⟩ : ↥(Q ⊓ K : Subgroup G)) ∈ ((phiH c hsQ).comp (phiH c hsQ)).ker := by
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    apply Subtype.ext
    rw [phiH_phiH]
    exact hN
  rw [← heq] at ha'
  obtain ⟨b, hb⟩ := ha'
  refine ⟨b, b.2, ?_⟩
  have := congrArg Subtype.val hb
  rw [phiH_apply] at this
  exact this.symm

theorem zpow_pow_three {x : G} (hx : x ^ 3 = 1) (k : ℤ) : (x ^ k) ^ 3 = 1 := by
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

theorem exists_conj_mem_A (c : Ctx E A e K Q) {x : G} (hxQ : x ∈ Q) (hx3 : x ^ 3 = 1)
    (hxP : x ∉ (Q ⊓ K : Subgroup G) ⊔ centBar 3 Q K) : ∃ q ∈ Q, q * x * q⁻¹ ∈ A := by
  obtain ⟨t, htA, htP⟩ := exists_t c
  have htQ : t ∈ Q := c.hAQ htA
  have ht3 : t ^ 3 = 1 := c.hAel.2 t htA
  obtain ⟨n, hn, k, rfl⟩ := exists_decomp c htQ ht3 htP hxQ
  have hcent : (Q ⊓ K : Subgroup G) ≤ Subgroup.centralizer (centBar 3 Q K : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact c.comm_centBar_Q0 hu ha
  obtain ⟨a, ha, u, hu, rfl⟩ := exists_mul_of_mem_sup hcent hn
  have hsQ : t ^ k ∈ Q := Q.zpow_mem htQ k
  have hs3 : (t ^ k) ^ 3 = 1 := zpow_pow_three ht3 k
  have hsP : t ^ k ∉ (Q ⊓ K : Subgroup G) ⊔ centBar 3 Q K := by
    intro hsP'
    exact hxP (mul_mem (mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hu)) hsP')
  have hXe : ∀ y ∈ Cg e, e * y = y * e := fun y hy =>
    Subgroup.mem_centralizer_iff.1 hy e (Set.mem_singleton e)
  have hue : u ∈ Subgroup.zpowers e :=
    Lemma113d.c_mem_zpowers_of_norm c.hQ c.hQ1 c.hXN c.hKX c.hKI c.hcyc hXe c.he3 c.he1 c.heQ ha
      hu hsQ hs3 hx3
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hue
  have huQ : ∀ q ∈ Q, e ^ j * q = q * e ^ j := fun q hq =>
    (Commute.zpow_left (show Commute e q from c.hQe q hq) j).eq
  have hu3 : (e ^ j) ^ 3 = 1 := zpow_pow_three c.he3 j
  have hN : a * (t ^ k * a * (t ^ k)⁻¹) * ((t ^ k) ^ 2 * a * ((t ^ k) ^ 2)⁻¹) = 1 := by
    have h1 : (a * e ^ j * t ^ k) ^ 3 = (a * t ^ k) ^ 3 := by
      have hc : Commute (a * t ^ k) (e ^ j) := (huQ _ (Q.mul_mem ha.1 hsQ)).symm
      rw [show a * e ^ j * t ^ k = a * t ^ k * e ^ j by
        rw [mul_assoc, huQ _ hsQ, ← mul_assoc], hc.mul_pow, hu3, mul_one]
    have h2 : (a * t ^ k) ^ 3 =
        a * (t ^ k * a * (t ^ k)⁻¹) * ((t ^ k) ^ 2 * a * ((t ^ k) ^ 2)⁻¹) * (t ^ k) ^ 3 := by
      simp only [pow_two, pow_three]
      group
    rw [h1, h2, hs3, mul_one] at hx3
    exact hx3
  obtain ⟨b, hb, hab⟩ := exists_phiH_eq c hsQ hs3 hsP ha hN
  refine ⟨b⁻¹, Q.inv_mem hb.1, ?_⟩
  have hbQ : (t ^ k * b * (t ^ k)⁻¹)⁻¹ ∈ Q :=
    Q.inv_mem (Q.mul_mem (Q.mul_mem hsQ hb.1) (Q.inv_mem hsQ))
  have key : b⁻¹ * (a * e ^ j * t ^ k) * b⁻¹⁻¹ = e ^ j * t ^ k := by
    rw [hab, inv_inv]
    calc b⁻¹ * (b * (t ^ k * b * (t ^ k)⁻¹)⁻¹ * e ^ j * t ^ k) * b
        = (t ^ k * b * (t ^ k)⁻¹)⁻¹ * e ^ j * t ^ k * b := by group
      _ = e ^ j * ((t ^ k * b * (t ^ k)⁻¹)⁻¹ * t ^ k * b) := by
        rw [← huQ _ hbQ]
        group
      _ = e ^ j * t ^ k := by group
  rw [key]
  exact A.mul_mem (A.zpow_mem c.heA j) (A.zpow_mem htA k)

theorem card_Z0_ge (c : Ctx E A e K Q) (hZ9 : 9 ≤ Nat.card ↥(E ⊓ A : Subgroup G)) :
    3 ≤ Nat.card ↥((E ⊓ A : Subgroup G) ⊓ (Q ⊓ K : Subgroup G)) := by
  have hcent : (Q ⊓ K : Subgroup G) ≤ Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) := by
    intro q hq
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact elemAbelian_comm c.hEel hz.1 (c.Q0_le_E hq)
  have hprod := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hcent
  have hsup : Nat.card ↥((E ⊓ A : Subgroup G) ⊔ (Q ⊓ K : Subgroup G)) ≤ 81 := by
    have := Subgroup.card_le_of_le (sup_le (inf_le_left : (E ⊓ A : Subgroup G) ≤ E) c.Q0_le_E)
    rw [c.hEcard] at this
    norm_num at this
    exact this
  rw [c.card_Q0] at hprod
  by_contra h
  push Not at h
  have h1 : Nat.card ↥((E ⊓ A : Subgroup G) ⊓ (Q ⊓ K : Subgroup G)) ≤ 2 := by omega
  have := Nat.mul_le_mul hsup h1
  omega

theorem mem_A_of_commute (c : Ctx E A e K Q) (hZ9 : 9 ≤ Nat.card ↥(E ⊓ A : Subgroup G))
    {y : G} (hyA : y ∈ A) (hyP : y ∉ (Q ⊓ K : Subgroup G) ⊔ centBar 3 Q K) {a : G}
    (ha : a ∈ (Q ⊓ K : Subgroup G)) (hay : a * y = y * a) : a ∈ A := by
  have hC3 := card_centralizer_le c (c.hAQ hyA) (c.hAel.2 y hyA) hyP
  have hle : (E ⊓ A : Subgroup G) ⊓ (Q ⊓ K : Subgroup G) ≤
      (Q ⊓ K : Subgroup G) ⊓ Subgroup.centralizer ({y} : Set G) := by
    intro z hz
    refine Subgroup.mem_inf.2 ⟨hz.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff.1 hw]
    exact elemAbelian_comm c.hAel hyA hz.1.2
  have heq := Subgroup.eq_of_le_of_card_ge hle (by have := card_Z0_ge c hZ9; omega)
  have haC : a ∈ (Q ⊓ K : Subgroup G) ⊓ Subgroup.centralizer ({y} : Set G) := by
    refine Subgroup.mem_inf.2 ⟨ha, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff.1 hw]
    exact hay.symm
  rw [← heq] at haC
  exact haC.1.2

theorem le_A_of_mem (c : Ctx E A e K Q) (hZ9 : 9 ≤ Nat.card ↥(E ⊓ A : Subgroup G))
    {F : Subgroup G} (hFQ : F ≤ Q) (hF : IsElemAbelian 3 F) {y : G} (hyF : y ∈ F) (hyA : y ∈ A)
    (hyP : y ∉ (Q ⊓ K : Subgroup G) ⊔ centBar 3 Q K) : F ≤ A := by
  intro w hw
  have hyQ := c.hAQ hyA
  have hy3 := c.hAel.2 y hyA
  obtain ⟨n, hn, k, rfl⟩ := exists_decomp c hyQ hy3 hyP (hFQ hw)
  have hnF : n ∈ F := by
    have h1 : n = n * y ^ k * (y ^ k)⁻¹ := by group
    rw [h1]
    exact F.mul_mem hw (F.inv_mem (F.zpow_mem hyF k))
  have hnE : n ∈ E := mem_E_of_mem_P c hn (hF.2 n hnF)
  have hcentE : (Q ⊓ K : Subgroup G) ≤
      Subgroup.centralizer ((Subgroup.zpowers e : Subgroup G) : Set G) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    exact (Commute.zpow_left (show Commute e q from c.hKe q hq.2) i).eq
  rw [c.hEeq] at hnE
  obtain ⟨a, ha, f, hf, rfl⟩ := exists_mul_of_mem_sup hcentE hnE
  have hfy : f * y = y * f := by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hf
    exact (Commute.zpow_left (show Commute e y from c.hQe y hyQ) i).eq
  have hny : a * f * y = y * (a * f) := elemAbelian_comm hF hnF hyF
  have hay : a * y = y * a := by
    calc a * y = a * (f * y * f⁻¹) := by rw [hfy, mul_inv_cancel_right]
      _ = a * f * y * f⁻¹ := by group
      _ = y * (a * f) * f⁻¹ := by rw [hny]
      _ = y * a := by group
  have haA := mem_A_of_commute c hZ9 hyA hyP ha hay
  exact A.mul_mem (A.mul_mem haA ((Subgroup.zpowers_le.2 c.heA) hf)) (A.zpow_mem hyA k)

theorem fusA (c : Ctx E A e K Q) (hZ9 : 9 ≤ Nat.card ↥(E ⊓ A : Subgroup G)) {x : G}
    (hx : x⁻¹ * e * x ∈ A) :
    ∃ n ∈ Subgroup.normalizer (A : Set G), n⁻¹ * e * n = x⁻¹ * e * x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSC : A.map (MulAut.conj x).toMonoidHom ≤ Cg e := by
    rintro _ ⟨a, ha, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.1 hy]
    have hcomm : (x⁻¹ * e * x) * a = a * (x⁻¹ * e * x) := elemAbelian_comm c.hAel hx ha
    show e * (x * a * x⁻¹) = x * a * x⁻¹ * e
    calc e * (x * a * x⁻¹) = x * ((x⁻¹ * e * x) * a) * x⁻¹ := by group
      _ = x * (a * (x⁻¹ * e * x)) * x⁻¹ := by rw [hcomm]
      _ = x * a * x⁻¹ * e := by group
  have hSp : IsPGroup 3 ↥(A.map (MulAut.conj x).toMonoidHom) :=
    (isPGroup_of_isElemAbelian' c.hAel).map _
  obtain ⟨c1, hc1C, hc1⟩ := Lemma113b.exists_conj_mem_of_isSylowIn c.hQ hSC hSp
  have hgA : ∀ a ∈ A, (c1 * x) * a * (c1 * x)⁻¹ ∈ Q := by
    intro a ha
    have := hc1 (x * a * x⁻¹) (Subgroup.mem_map.2 ⟨a, ha, rfl⟩)
    rw [show (c1 * x) * a * (c1 * x)⁻¹ = c1 * (x * a * x⁻¹) * c1⁻¹ by group]
    exact this
  obtain ⟨a0, ha0A, ha0P⟩ : ∃ a0 ∈ A,
      (c1 * x) * a0 * (c1 * x)⁻¹ ∉ (Q ⊓ K : Subgroup G) ⊔ centBar 3 Q K := by
    by_contra hcon
    push Not at hcon
    have hAle : A ≤ E.map (MulAut.conj (c1 * x)⁻¹).toMonoidHom := by
      intro a ha
      have h3 : ((c1 * x) * a * (c1 * x)⁻¹) ^ 3 = 1 := by
        rw [conj_pow, c.hAel.2 a ha]
        group
      have hmem : (c1 * x) * a * (c1 * x)⁻¹ ∈ E := mem_E_of_mem_P c (hcon a ha) h3
      refine Subgroup.mem_map.2 ⟨(c1 * x) * a * (c1 * x)⁻¹, hmem, ?_⟩
      show (c1 * x)⁻¹ * ((c1 * x) * a * (c1 * x)⁻¹) * (c1 * x)⁻¹⁻¹ = a
      group
    have hEl : IsElemAbelian 3 (E.map (MulAut.conj (c1 * x)⁻¹).toMonoidHom) :=
      Lemma113d.isElemAbelian_map_any _ c.hEel
    have heq := c.hAmax _ le_top hEl hAle
    have h1 : Nat.card ↥(E.map (MulAut.conj (c1 * x)⁻¹).toMonoidHom) = 81 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj (c1 * x)⁻¹).injective, c.hEcard]
      norm_num
    rw [heq, c.hAcard] at h1
    norm_num at h1
  have hyQ : (c1 * x) * a0 * (c1 * x)⁻¹ ∈ Q := hgA a0 ha0A
  have hy3 : ((c1 * x) * a0 * (c1 * x)⁻¹) ^ 3 = 1 := by
    rw [conj_pow, c.hAel.2 a0 ha0A]
    group
  obtain ⟨q, hqQ, hqy⟩ := exists_conj_mem_A c hyQ hy3 ha0P
  have hqyP : q * ((c1 * x) * a0 * (c1 * x)⁻¹) * q⁻¹ ∉ (Q ⊓ K : Subgroup G) ⊔ centBar 3 Q K := by
    intro h
    apply ha0P
    have := P_conj c (Q.inv_mem hqQ) h
    rwa [show q⁻¹ * (q * ((c1 * x) * a0 * (c1 * x)⁻¹) * q⁻¹) * q⁻¹⁻¹ =
      (c1 * x) * a0 * (c1 * x)⁻¹ by group] at this
  have hFQ : A.map (MulAut.conj (q * (c1 * x))).toMonoidHom ≤ Q := by
    rintro _ ⟨a, ha, rfl⟩
    show q * (c1 * x) * a * (q * (c1 * x))⁻¹ ∈ Q
    rw [show q * (c1 * x) * a * (q * (c1 * x))⁻¹ = q * ((c1 * x) * a * (c1 * x)⁻¹) * q⁻¹ by group]
    exact Q.mul_mem (Q.mul_mem hqQ (hgA a ha)) (Q.inv_mem hqQ)
  have hFel : IsElemAbelian 3 (A.map (MulAut.conj (q * (c1 * x))).toMonoidHom) :=
    Lemma113d.isElemAbelian_map_any _ c.hAel
  have hyF : q * ((c1 * x) * a0 * (c1 * x)⁻¹) * q⁻¹ ∈
      A.map (MulAut.conj (q * (c1 * x))).toMonoidHom := by
    refine Subgroup.mem_map.2 ⟨a0, ha0A, ?_⟩
    show q * (c1 * x) * a0 * (q * (c1 * x))⁻¹ = q * ((c1 * x) * a0 * (c1 * x)⁻¹) * q⁻¹
    group
  have hFA := le_A_of_mem c hZ9 hFQ hFel hyF hqy hqyP
  refine ⟨q * (c1 * x), mem_normalizer_of_conj_le fun a ha =>
    hFA (Subgroup.mem_map.2 ⟨a, ha, rfl⟩), ?_⟩
  have hqe : e * q = q * e := c.hQe q hqQ
  have hc1e : e * c1 = c1 * e := Subgroup.mem_centralizer_iff.1 hc1C e (Set.mem_singleton e)
  calc (q * (c1 * x))⁻¹ * e * (q * (c1 * x)) = x⁻¹ * c1⁻¹ * (q⁻¹ * (e * q)) * c1 * x := by group
    _ = x⁻¹ * (c1⁻¹ * (e * c1)) * x := by rw [hqe]; group
    _ = x⁻¹ * e * x := by rw [hc1e]; group

theorem comm_of_card_three {T : Type*} [Group T] (hT : Nat.card T = 3) (u v : T) :
    u * v = v * u := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsCyclic T := isCyclic_of_prime_card hT
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := T)
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg u)
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg v)
  exact ((Commute.refl g).zpow_zpow i j).eq

theorem comm_mem_Z (c : Ctx E A e K Q)
    (hNK : Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G) ≤
      Subgroup.normalizer (K : Set G))
    {y : G} (hyNe : y ∈ Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G))
    (hyA : y ∈ Subgroup.normalizer (A : Set G)) {a : G} (ha : a ∈ A) :
    y * a * y⁻¹ * a⁻¹ ∈ E ⊓ A := by
  obtain ⟨e0⟩ := c.hKI
  have hxA : y * a * y⁻¹ * a⁻¹ ∈ A :=
    A.mul_mem ((Subgroup.mem_normalizer_iff.1 hyA a).1 ha) (A.inv_mem ha)
  by_contra hnot
  have hxQ : y * a * y⁻¹ * a⁻¹ ∈ Q := c.hAQ hxA
  have hx3 : (y * a * y⁻¹ * a⁻¹) ^ 3 = 1 := c.hAel.2 _ hxA
  have hxP : y * a * y⁻¹ * a⁻¹ ∉ (Q ⊓ K : Subgroup G) ⊔ centBar 3 Q K := fun hP =>
    hnot (mem_Z_of_mem_P c hxA hP)
  have hU27 := Lemma113d.Ubar_card c.hQ c.hQ1 c.hXN c.hKX c.hKI
  apply Lemma113d.galHom_rho_ne_one e0 c.hQp c.hQK hU27 hxQ hx3 hxP
  have hyK : y ∈ Subgroup.normalizer (K : Set G) := hNK hyNe
  have haK : a ∈ Subgroup.normalizer (K : Set G) := c.hQK (c.hAQ ha)
  have hcomm := comm_of_card_three Lemma113d.finite_ringAut_card
  have hsplit : (⟨y * a * y⁻¹ * a⁻¹, c.hQK hxQ⟩ : ↥(Subgroup.normalizer (K : Set G))) =
      ⟨y, hyK⟩ * ⟨a, haK⟩ * ⟨y, hyK⟩⁻¹ * ⟨a, haK⟩⁻¹ := rfl
  rw [hsplit]
  simp only [map_mul, map_inv]
  rw [hcomm ((Lemma113d.galHom e0) ((barAut 3 K) ⟨y, hyK⟩))
    ((Lemma113d.galHom e0) ((barAut 3 K) ⟨a, haK⟩))]
  group

theorem sylow_normalizer_Z (c : Ctx E A e K Q)
    (hQZ : Q ≤ Subgroup.centralizer ((E ⊓ A : Subgroup G) : Set G))
    (hN : Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G)) :
    IsSylowIn 3 (Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G)) Q := by
  have hSN := Lemma113d.isSylowIn_normalizer_zpowers rfl c.hQ c.he3 c.he1
  exact ⟨hQZ.trans (Subgroup.centralizer_le_normalizer _), c.hQp, fun R' hR' hR'p hQR' =>
    hSN.2.2 R' (hR'.trans hN) hR'p hQR'⟩

theorem commute_of_mem_normalizer_Z (c : Ctx E A e K Q)
    (hQZ : Q ≤ Subgroup.centralizer ((E ⊓ A : Subgroup G) : Set G))
    (hN : Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G))
    {m : G} (hm : m ∈ Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G)) (hm3 : m ^ 3 = 1)
    {z : G} (hz : z ∈ E ⊓ A) : m * z * m⁻¹ = z := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSyl := sylow_normalizer_Z c hQZ hN
  have hS : Subgroup.zpowers m ≤ Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.2 hm
  have hSp : IsPGroup 3 ↥(Subgroup.zpowers m) :=
    isPGroup_of_isElemAbelian' (l113_isElemAbelian_zpowers hm3)
  obtain ⟨g, hgN, hg⟩ := Lemma113b.exists_conj_mem_of_isSylowIn hSyl hS hSp
  have hgm : g * m * g⁻¹ ∈ Q := hg m (Subgroup.mem_zpowers m)
  have hgz : g * z * g⁻¹ ∈ E ⊓ A := (Subgroup.mem_normalizer_iff.1 hgN z).1 hz
  have hc : (g * z * g⁻¹) * (g * m * g⁻¹) = (g * m * g⁻¹) * (g * z * g⁻¹) :=
    Subgroup.mem_centralizer_iff.1 (hQZ hgm) _ hgz
  have h1 : g * (m * z * m⁻¹) * g⁻¹ = g * z * g⁻¹ := by
    calc g * (m * z * m⁻¹) * g⁻¹ = (g * m * g⁻¹) * (g * z * g⁻¹) * (g * m * g⁻¹)⁻¹ := by group
      _ = (g * z * g⁻¹) * (g * m * g⁻¹) * (g * m * g⁻¹)⁻¹ := by rw [← hc]
      _ = g * z * g⁻¹ := by group
  exact mul_left_cancel (mul_right_cancel h1)

theorem exists_r (c : Ctx E A e K Q) (hZ9 : 9 ≤ Nat.card ↥(E ⊓ A : Subgroup G)) :
    ∃ z0 ∈ E ⊓ A, z0 ≠ 1 ∧ ∃ r ∈ (Q ⊓ K : Subgroup G),
      ∀ a ∈ A, r * a * r⁻¹ * a⁻¹ ∈ Subgroup.zpowers z0 ∧ (r * a * r⁻¹ = a → a ∈ E ⊓ A) := by
  obtain ⟨t, htA, htP⟩ := exists_t c
  have htQ : t ∈ Q := c.hAQ htA
  have ht3 : t ^ 3 = 1 := c.hAel.2 t htA
  have h3 := card_Z0_ge c hZ9
  obtain ⟨z0, hz0, hz01⟩ : ∃ z0 ∈ (E ⊓ A : Subgroup G) ⊓ (Q ⊓ K : Subgroup G), z0 ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : (E ⊓ A : Subgroup G) ⊓ (Q ⊓ K : Subgroup G) = ⊥ :=
      eq_bot_iff.2 fun x hx => Subgroup.mem_bot.2 (hcon x hx)
    rw [hbot, Subgroup.card_bot] at h3
    omega
  have hz0A : z0 ∈ A := hz0.1.2
  have hz03 : z0 ^ 3 = 1 := c.hAel.2 z0 hz0A
  have hz0t : Commute t z0 := elemAbelian_comm c.hAel htA hz0A
  have hN : z0 * (t * z0 * t⁻¹) * (t ^ 2 * z0 * (t ^ 2)⁻¹) = 1 := by
    have h1 : t * z0 * t⁻¹ = z0 := by rw [hz0t.eq]; group
    have h2 : t ^ 2 * z0 * (t ^ 2)⁻¹ = z0 := by rw [(hz0t.pow_left 2).eq]; group
    rw [h1, h2, ← pow_three', hz03]
  obtain ⟨r, hr, hrz⟩ := exists_phiH_eq c htQ ht3 htP hz0.2 hN
  have hrt : r * t * r⁻¹ = z0 * t := by
    rw [hrz]
    group
  refine ⟨z0, hz0.1, hz01, r, hr, fun a ha => ?_⟩
  obtain ⟨n, hn, k, rfl⟩ := exists_decomp c htQ ht3 htP (c.hAQ ha)
  have hnA : n ∈ A := by
    have h1 : n = n * t ^ k * (t ^ k)⁻¹ := by group
    rw [h1]
    exact A.mul_mem ha (A.inv_mem (A.zpow_mem htA k))
  have hnZ : n ∈ E ⊓ A := mem_Z_of_mem_P c hnA hn
  have hrn : r * n = n * r := elemAbelian_comm c.hEel (c.Q0_le_E hr) hnZ.1
  have hrtk : r * t ^ k * r⁻¹ = z0 ^ k * t ^ k := by
    rw [← conj_zpow, hrt, Commute.mul_zpow hz0t.symm k]
  have hnz0 : Commute n (z0 ^ k) :=
    (show Commute n z0 from elemAbelian_comm c.hAel hnA hz0A).zpow_right k
  have hconj : r * (n * t ^ k) * r⁻¹ = z0 ^ k * (n * t ^ k) := by
    calc r * (n * t ^ k) * r⁻¹ = (r * n * r⁻¹) * (r * t ^ k * r⁻¹) := by group
      _ = n * (z0 ^ k * t ^ k) := by rw [hrtk, hrn]; group
      _ = z0 ^ k * (n * t ^ k) := by rw [← mul_assoc, hnz0.eq, mul_assoc]
  constructor
  · rw [hconj, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers z0 k
  · intro hfix
    rw [hconj] at hfix
    have hzk : z0 ^ k = 1 := by
      have h' : z0 ^ k * (n * t ^ k) = 1 * (n * t ^ k) := by rw [one_mul]; exact hfix
      exact mul_right_cancel h'
    have hord : orderOf z0 = 3 := orderOf_eq_prime hz03 hz01
    have h3k : (3 : ℤ) ∣ k := by
      have := orderOf_dvd_iff_zpow_eq_one.2 hzk
      rw [hord] at this
      exact_mod_cast this
    obtain ⟨m, rfl⟩ := h3k
    have htk : t ^ (3 * m) = 1 := by
      rw [zpow_mul]
      have : t ^ (3 : ℤ) = 1 := by exact_mod_cast ht3
      rw [this, one_zpow]
    rw [htk, mul_one]
    exact hnZ

theorem normalize_sign {ρ u v : G} (hρA : ρ ∈ Subgroup.normalizer (A : Set G))
    (hu3 : u ^ 3 = 1) (hρu : ρ * u * ρ⁻¹ = u)
    (hρa : ∀ a ∈ A, ρ * a * ρ⁻¹ * a⁻¹ ∈ Subgroup.zpowers u)
    (hv : v ∈ A) (hρv : ρ * v * ρ⁻¹ * v⁻¹ ≠ 1) :
    ∃ ρ' ∈ Subgroup.normalizer (A : Set G), ρ' * u * ρ'⁻¹ = u ∧ ρ' * v * ρ'⁻¹ = u * v ∧
      (∀ a ∈ A, ρ' * a * ρ'⁻¹ * a⁻¹ ∈ Subgroup.zpowers u) ∧
      (∀ z : G, ρ * z * ρ⁻¹ = z → ρ' * z * ρ'⁻¹ = z) := by
  rcases mem_zpowers_cases hu3 (hρa v hv) with h | h | h
  · exact absurd h hρv
  · refine ⟨ρ, hρA, hρu, ?_, hρa, fun z hz => hz⟩
    calc ρ * v * ρ⁻¹ = (ρ * v * ρ⁻¹ * v⁻¹) * v := by group
      _ = u * v := by rw [h]
  · have hρu1 : ρ⁻¹ * u * ρ = u := by
      calc ρ⁻¹ * u * ρ = ρ⁻¹ * (ρ * u * ρ⁻¹) * ρ := by rw [hρu]
        _ = u := by group
    have hρu2 : ρ⁻¹ * u⁻¹ * ρ = u⁻¹ := by
      calc ρ⁻¹ * u⁻¹ * ρ = (ρ⁻¹ * u * ρ)⁻¹ := by group
        _ = u⁻¹ := by rw [hρu1]
    have h1 : ρ * v * ρ⁻¹ = u⁻¹ * v := by
      calc ρ * v * ρ⁻¹ = (ρ * v * ρ⁻¹ * v⁻¹) * v := by group
        _ = u⁻¹ * v := by rw [h]
    refine ⟨ρ⁻¹, inv_mem hρA, by rw [inv_inv]; exact hρu1, ?_, ?_, ?_⟩
    · rw [inv_inv]
      calc ρ⁻¹ * v * ρ = u * (u⁻¹ * (ρ⁻¹ * v * ρ)) := by group
        _ = u * ((ρ⁻¹ * u⁻¹ * ρ) * (ρ⁻¹ * v * ρ)) := by rw [hρu2]
        _ = u * (ρ⁻¹ * (u⁻¹ * v) * ρ) := by group
        _ = u * (ρ⁻¹ * (ρ * v * ρ⁻¹) * ρ) := by rw [h1]
        _ = u * v := by group
    · intro a ha
      have hb : ρ⁻¹ * a * ρ ∈ A := by
        have := (Subgroup.mem_normalizer_iff.1 (inv_mem hρA) a).1 ha
        rwa [inv_inv] at this
      have hmem := hρa _ hb
      have heq : ρ⁻¹ * a * ρ⁻¹⁻¹ * a⁻¹ = (ρ * (ρ⁻¹ * a * ρ) * ρ⁻¹ * (ρ⁻¹ * a * ρ)⁻¹)⁻¹ := by group
      rw [heq]
      exact inv_mem hmem
    · intro z hz
      rw [inv_inv]
      calc ρ⁻¹ * z * ρ = ρ⁻¹ * (ρ * z * ρ⁻¹) * ρ := by rw [hz]
        _ = z := by group

theorem key_z0z1 {z0 z1 : G} (hc : z1 * z0 = z0 * z1) (hz03 : z0 ^ 3 = 1) (hz13 : z1 ^ 3 = 1) :
    z0 * z1 * z0 * (z0 * z1) = z1⁻¹ := by
  have hz03' : z0 * z0 * z0 = 1 := by rw [← pow_three']; exact hz03
  have hz1inv : z1 * z1 = z1⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_three']; exact hz13)
  calc z0 * z1 * z0 * (z0 * z1) = z0 * (z1 * z0) * z0 * z1 := by group
    _ = z0 * (z0 * z1) * z0 * z1 := by rw [hc]
    _ = z0 * z0 * (z1 * z0) * z1 := by group
    _ = z0 * z0 * (z0 * z1) * z1 := by rw [hc]
    _ = (z0 * z0 * z0) * (z1 * z1) := by group
    _ = z1⁻¹ := by rw [hz03', one_mul, hz1inv]

theorem sl23_inv {r1 r2 z0 z1 : G} (hc : z1 * z0 = z0 * z1) (hz03 : z0 ^ 3 = 1)
    (hz13 : z1 ^ 3 = 1) (e1 : r1 * z0 * r1⁻¹ = z0) (e2 : r1 * z1 * r1⁻¹ = z0 * z1)
    (e3 : r2 * z0 * r2⁻¹ = z1 * z0) (e4 : r2 * z1 * r2⁻¹ = z1) :
    (r1 * r2 * r1 * r2) * z1 * (r1 * r2 * r1 * r2)⁻¹ = z1⁻¹ := by
  have hcm : ∀ g a b : G, g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := fun g a b => by
    group
  have hy : (r1 * r2 * r1 * r2) * z1 * (r1 * r2 * r1 * r2)⁻¹ =
      r1 * (r2 * (r1 * (r2 * z1 * r2⁻¹) * r1⁻¹) * r2⁻¹) * r1⁻¹ := by group
  rw [hy, e4, e2, hcm r2 z0 z1, e3, e4, hcm r1 (z1 * z0) z1, hcm r1 z1 z0, e2, e1]
  exact key_z0z1 hc hz03 hz13

theorem sl23_norm {r1 r2 z0 z1 z : G} (hc : z1 * z0 = z0 * z1) (hz03 : z0 ^ 3 = 1)
    (hz13 : z1 ^ 3 = 1) (e1 : r1 * z0 * r1⁻¹ = z0) (e2 : r1 * z1 * r1⁻¹ = z0 * z1)
    (e3 : r2 * z0 * r2⁻¹ = z1 * z0) (e4 : r2 * z1 * r2⁻¹ = z1) {j : ℤ}
    (e5 : r2 * z * r2⁻¹ = z1 ^ j * z) (e6 : r1 * z * r1⁻¹ = z) :
    (r1 * r2 * r1 * r2) * z * (r1 * r2 * r1 * r2)⁻¹ = z0 ^ j * z := by
  have hcm : ∀ g a b : G, g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := fun g a b => by
    group
  have hcz : ∀ (g a : G) (i : ℤ), g * a ^ i * g⁻¹ = (g * a * g⁻¹) ^ i := fun g a i =>
    conj_zpow.symm
  have hy : (r1 * r2 * r1 * r2) * z * (r1 * r2 * r1 * r2)⁻¹ =
      r1 * (r2 * (r1 * (r2 * z * r2⁻¹) * r1⁻¹) * r2⁻¹) * r1⁻¹ := by group
  rw [hy, e5, hcm r1 (z1 ^ j) z, hcz r1 z1 j, e2, e6, hcm r2 ((z0 * z1) ^ j) z,
    hcz r2 (z0 * z1) j, hcm r2 z0 z1, e3, e4, e5, hcm r1 ((z1 * z0 * z1) ^ j) (z1 ^ j * z),
    hcz r1 (z1 * z0 * z1) j, hcm r1 (z1 * z0) z1, hcm r1 z1 z0, hcm r1 (z1 ^ j) z, hcz r1 z1 j,
    e2, e1, e6, key_z0z1 hc hz03 hz13, Commute.mul_zpow (show Commute z0 z1 from hc.symm) j,
    inv_zpow]
  have hcc : Commute (z0 ^ j) (z1 ^ j) := (show Commute z0 z1 from hc.symm).zpow_zpow j j
  calc (z1 ^ j)⁻¹ * (z0 ^ j * z1 ^ j * z) = (z1 ^ j)⁻¹ * (z1 ^ j * z0 ^ j * z) := by rw [hcc.eq]
    _ = z0 ^ j * z := by group

theorem caseA (c : Ctx E A e K Q)
    (hQZ : Q ≤ Subgroup.centralizer ((E ⊓ A : Subgroup G) : Set G))
    (hN : Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G))
    {z0 r : G} (hr : r ∈ (Q ⊓ K : Subgroup G))
    (hrA : ∀ a ∈ A, r * a * r⁻¹ * a⁻¹ ∈ Subgroup.zpowers z0 ∧ (r * a * r⁻¹ = a → a ∈ E ⊓ A))
    {n : G} (hn : n ∈ Subgroup.normalizer (A : Set G)) (hnz : n⁻¹ * z0 * n ∈ E ⊓ A) :
    n ∈ Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) := by
  have hmN : n⁻¹ * r * n ∈ Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) := by
    apply mem_normalizer_of_conj_le
    intro z hz
    have hw : n * z * n⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 hn z).1 hz.2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hrA _ hw).1
    have hrw : r * (n * z * n⁻¹) * r⁻¹ = z0 ^ j * (n * z * n⁻¹) := by
      rw [hj]
      group
    have hcz : (n⁻¹ * z0 * n) ^ j = n⁻¹ * z0 ^ j * n := by
      have := conj_zpow (i := j) (a := n⁻¹) (b := z0)
      rwa [inv_inv] at this
    have heq : (n⁻¹ * r * n) * z * (n⁻¹ * r * n)⁻¹ = (n⁻¹ * z0 * n) ^ j * z := by
      calc (n⁻¹ * r * n) * z * (n⁻¹ * r * n)⁻¹ = n⁻¹ * (r * (n * z * n⁻¹) * r⁻¹) * n := by group
        _ = n⁻¹ * (z0 ^ j * (n * z * n⁻¹)) * n := by rw [hrw]
        _ = (n⁻¹ * z0 * n) ^ j * z := by rw [hcz]; group
    rw [heq]
    exact (E ⊓ A : Subgroup G).mul_mem ((E ⊓ A : Subgroup G).zpow_mem hnz j) hz
  have hm3 : (n⁻¹ * r * n) ^ 3 = 1 := by
    have := conj_pow (i := 3) (a := n⁻¹) (b := r)
    rw [inv_inv] at this
    rw [this, c.Q0_elemAbelian.2 r hr]
    group
  apply mem_normalizer_of_conj_le
  intro z hz
  have hfix := commute_of_mem_normalizer_Z c hQZ hN hmN hm3 hz
  have hw : n * z * n⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 hn z).1 hz.2
  apply (hrA _ hw).2
  calc r * (n * z * n⁻¹) * r⁻¹ = n * ((n⁻¹ * r * n) * z * (n⁻¹ * r * n)⁻¹) * n⁻¹ := by group
    _ = n * z * n⁻¹ := by rw [hfix]

theorem caseC (c : Ctx E A e K Q)
    (hNK : Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G) ≤
      Subgroup.normalizer (K : Set G))
    (hN : Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G))
    {z0 r : G} (hz0 : z0 ∈ E ⊓ A) (hr : r ∈ (Q ⊓ K : Subgroup G))
    (hrA : ∀ a ∈ A, r * a * r⁻¹ * a⁻¹ ∈ Subgroup.zpowers z0 ∧ (r * a * r⁻¹ = a → a ∈ E ⊓ A))
    {n : G} (hn : n ∈ Subgroup.normalizer (A : Set G)) (h1 : n⁻¹ * z0 * n ∉ E ⊓ A)
    (h2 : n * z0 * n⁻¹ ∉ E ⊓ A) : False := by
  have hz0A : z0 ∈ A := hz0.2
  have hz03 : z0 ^ 3 = 1 := c.hAel.2 z0 hz0A
  have hz1A : n * z0 * n⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 hn z0).1 hz0A
  have hz13 : (n * z0 * n⁻¹) ^ 3 = 1 := c.hAel.2 _ hz1A
  have hrZ : ∀ z ∈ E ⊓ A, r * z * r⁻¹ = z := fun z hz => by
    rw [elemAbelian_comm c.hEel (c.Q0_le_E hr) hz.1]
    group
  have hrN : r ∈ Subgroup.normalizer (A : Set G) := by
    apply mem_normalizer_of_conj_le
    intro a ha
    have h' : r * a * r⁻¹ = (r * a * r⁻¹ * a⁻¹) * a := by group
    rw [h']
    exact A.mul_mem ((Subgroup.zpowers_le.2 hz0A) (hrA a ha).1) ha
  obtain ⟨r1, hr1N, hr1z0, hr1z1, -, hr1Z⟩ := normalize_sign hrN hz03 (hrZ z0 hz0)
    (fun a ha => (hrA a ha).1) hz1A (fun h => h2 ((hrA _ hz1A).2 (mul_inv_eq_one.1 h)))
  have hr'N : n * r * n⁻¹ ∈ Subgroup.normalizer (A : Set G) :=
    mul_mem (mul_mem hn hrN) (inv_mem hn)
  have hr'z1 : (n * r * n⁻¹) * (n * z0 * n⁻¹) * (n * r * n⁻¹)⁻¹ = n * z0 * n⁻¹ := by
    calc (n * r * n⁻¹) * (n * z0 * n⁻¹) * (n * r * n⁻¹)⁻¹ = n * (r * z0 * r⁻¹) * n⁻¹ := by group
      _ = n * z0 * n⁻¹ := by rw [hrZ z0 hz0]
  have hr'A : ∀ a ∈ A, (n * r * n⁻¹) * a * (n * r * n⁻¹)⁻¹ * a⁻¹ ∈
      Subgroup.zpowers (n * z0 * n⁻¹) ∧
      ((n * r * n⁻¹) * a * (n * r * n⁻¹)⁻¹ = a → n⁻¹ * a * n ∈ E ⊓ A) := by
    intro a ha
    have hb : n⁻¹ * a * n ∈ A := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hn) a).1 ha
      rwa [inv_inv] at this
    obtain ⟨hb1, hb2⟩ := hrA _ hb
    constructor
    · obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hb1
      refine Subgroup.mem_zpowers_iff.2 ⟨j, ?_⟩
      rw [conj_zpow, hj]
      group
    · intro hfix
      apply hb2
      calc r * (n⁻¹ * a * n) * r⁻¹ = n⁻¹ * ((n * r * n⁻¹) * a * (n * r * n⁻¹)⁻¹) * n := by group
        _ = n⁻¹ * a * n := by rw [hfix]
  obtain ⟨r2, hr2N, hr2z1, hr2z0, hr2A, -⟩ := normalize_sign hr'N hz13 hr'z1
    (fun a ha => (hr'A a ha).1) hz0A (fun h => h1 ((hr'A z0 hz0A).2 (mul_inv_eq_one.1 h)))
  set z1 := n * z0 * n⁻¹ with hz1def
  have hc : z1 * z0 = z0 * z1 := elemAbelian_comm c.hAel hz1A hz0A
  have hyA : r1 * r2 * r1 * r2 ∈ Subgroup.normalizer (A : Set G) :=
    mul_mem (mul_mem (mul_mem hr1N hr2N) hr1N) hr2N
  have hyZ : r1 * r2 * r1 * r2 ∈ Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) := by
    apply mem_normalizer_of_conj_le
    intro z hz
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hr2A z hz.2)
    have e5 : r2 * z * r2⁻¹ = z1 ^ j * z := by rw [hj]; group
    rw [sl23_norm hc hz03 hz13 hr1z0 hr1z1 hr2z0 hr2z1 e5 (hr1Z z (hrZ z hz))]
    exact (E ⊓ A : Subgroup G).mul_mem ((E ⊓ A : Subgroup G).zpow_mem hz0 j) hz
  have hmem := comm_mem_Z c hNK (hN hyZ) hyA hz1A
  rw [sl23_inv hc hz03 hz13 hr1z0 hr1z1 hr2z0 hr2z1] at hmem
  have hzz : z1⁻¹ * z1⁻¹ = z1 := by
    calc z1⁻¹ * z1⁻¹ = z1⁻¹ * z1⁻¹ * z1 ^ 3 := by rw [hz13, mul_one]
      _ = z1 := by group
  rw [hzz] at hmem
  exact h2 hmem

theorem core (c : Ctx E A e K Q)
    (hNK : Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G) ≤
      Subgroup.normalizer (K : Set G))
    (hQZ : Q ≤ Subgroup.centralizer ((E ⊓ A : Subgroup G) : Set G))
    (hZ9 : 9 ≤ Nat.card ↥(E ⊓ A : Subgroup G))
    (hN : Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G)) :
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) := by
  obtain ⟨z0, hz0, -, r, hr, hrA⟩ := exists_r c hZ9
  intro n hn
  by_cases h1 : n⁻¹ * z0 * n ∈ E ⊓ A
  · exact caseA c hQZ hN hr hrA hn h1
  · by_cases h2 : n * z0 * n⁻¹ ∈ E ⊓ A
    · have h := caseA c hQZ hN hr hrA (inv_mem hn) (by rwa [inv_inv])
      simpa using inv_mem h
    · exact (caseC c hNK hN hz0 hr hrA hn h1 h2).elim

theorem card_inf_ge_nine {m : ℕ} {B₀ M : Subgroup G} {a : G} (h : Cfg113 G m B₀ M E A a e K Q)
    (hAel : IsElemAbelian 3 A) : 9 ≤ Nat.card ↥(E ⊓ A : Subgroup G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hel : IsElemAbelian 3 (E ⊓ A : Subgroup G) := isElemAbelian_mono hAel inf_le_right
  rw [l113_card_eq_pow_pRank hel]
  calc 9 = 3 ^ 2 := by norm_num
    _ ≤ 3 ^ CFSG.Open.pRank 3 (E ⊓ A) := Nat.pow_le_pow_right (by norm_num) h.pair.1.2.2

end Lemma113Claims.B

theorem inputB_order3_holds : Lemma113e.InputB_order3 := by
  intro G _ _ m B₀ M E A a e K Q h hA x hxQ hx3 _
  have c := Lemma113Claims.Ctx.of_cfg h hA
  by_cases hxP : x ∈ (Q ⊓ K : Subgroup G) ⊔ centBar 3 Q K
  · exact Or.inl (Lemma113Claims.B.mem_E_of_mem_P c hxP hx3)
  · obtain ⟨q, hqQ, hq⟩ := Lemma113Claims.B.exists_conj_mem_A c hxQ hx3 hxP
    exact Or.inr ⟨q, hqQ, mem_gLBConj.2 hq⟩

theorem inputB_fusA_holds : Lemma113e.InputB_fusA := by
  intro G _ _ m B₀ M E A a e K Q h hA x hx
  have c := Lemma113Claims.Ctx.of_cfg h hA
  exact Lemma113Claims.B.fusA c (Lemma113Claims.B.card_inf_ge_nine h c.hAel) hx

theorem inputB_core_holds : Lemma113e.InputB_core := by
  intro G _ _ m B₀ M E A a e K Q h hA hN
  have c := Lemma113Claims.Ctx.of_cfg h hA
  have hNK := Lemma113d.normalizer_zpowers_le_normalizer_K rfl c.hQ c.hQ1 c.hXN c.hKX h.hK.1
    c.hKI c.he3 c.he1 hA.2.1 (c.hAQ h.ha.1) (lemma113_ii_piece0_holds h)
  exact Lemma113Claims.B.core c hNK (Lemma113e.pieceB_SylZ_of h hA).1
    (Lemma113Claims.B.card_inf_ge_nine h c.hAel) hN

theorem lemma113_ii_pieceB_holds' : Lemma113_ii_pieceBStatement :=
  Lemma113e.pieceB_statement_of_inputs inputB_order3_holds inputB_fusA_holds inputB_core_holds

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

end
