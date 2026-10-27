module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop126
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma119
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911TypeProof
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec12c
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.Input18
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)

namespace Prop126b

section TP3

variable {G : Type} [Group G] [Finite G]

theorem pCore_two_le_primeCore_three (H : Type) [Group H] [Finite H] :
    CFSG.pCore 2 H ≤ GLAPPrimeCore 3 H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_sSup ⟨CFSG.LieType.BorelTits.pCore_normal 2, ?_⟩
  obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := H)).exists_card_eq
  rw [hk]
  exact Nat.Coprime.pow_right k (by norm_num)

theorem isQuasisimple_barOf_of_twoPrimeComp {X J : Subgroup G} (hJ : IsTwoPrimeComp X J)
    (h3 : 3 ∣ Nat.card ↥J) : CFSG.Open.IsQuasisimple (↥J ⧸ GLAPPrimeCore 3 ↥J) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq2 : CFSG.Open.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (quotEquivTwoImage hJ.1 hJ.2.1).symm hJ.2.2.2.2.2
  let f : (↥J ⧸ CFSG.pCore 2 ↥J) →* (↥J ⧸ GLAPPrimeCore 3 ↥J) :=
    QuotientGroup.map _ _ (MonoidHom.id ↥J) (by
      rw [Subgroup.comap_id]
      exact pCore_two_le_primeCore_three ↥J)
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨QuotientGroup.mk x, rfl⟩
  haveI : Nontrivial (↥J ⧸ GLAPPrimeCore 3 ↥J) := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    haveI : Unique (↥J ⧸ GLAPPrimeCore 3 ↥J) := ⟨⟨1⟩, fun a => Subsingleton.elim _ _⟩
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (GLAPPrimeCore 3 ↥J)
    have h2 : Nat.card (↥J ⧸ GLAPPrimeCore 3 ↥J) = 1 := Nat.card_unique
    rw [h2, one_mul] at h1
    have hcop : Nat.Coprime 3 (Nat.card ↥(GLAPPrimeCore 3 ↥J)) := CFSG.pPrimeCore_coprime_card
    rw [h1] at h3
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcop h3
  exact CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.isQuasisimple_of_surjective_of_nontrivial
    hq2 f hf

theorem eq_top_of_perfect_of_solvable {Γ : Type*} [Group Γ] (hΓ : commutator Γ = ⊤)
    {M₀ N : Subgroup Γ} [M₀.Normal] (hN : Group.IsSolvable ↥N)
    (hsplit : ∀ g : Γ, ∃ m ∈ M₀, ∃ n ∈ N, g = m * n) : M₀ = ⊤ := by
  let ψ : ↥N →* Γ ⧸ M₀ := (QuotientGroup.mk' M₀).comp N.subtype
  have hψ : Function.Surjective ψ := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨m, hm, n, hn, rfl⟩ := hsplit g
    refine ⟨⟨n, hn⟩, ?_⟩
    show (QuotientGroup.mk' M₀) n = (QuotientGroup.mk' M₀) (m * n)
    have h1 : (QuotientGroup.mk' M₀) m = 1 := (QuotientGroup.eq_one_iff m).2 hm
    rw [map_mul, h1, one_mul]
  haveI : Group.IsSolvable ↥N := hN
  haveI : Group.IsSolvable (Γ ⧸ M₀) := solvable_of_surjective hψ
  have hperf : commutator (Γ ⧸ M₀) = ⊤ := by
    have h1 : (commutator Γ).map (QuotientGroup.mk' M₀) = commutator (Γ ⧸ M₀) := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective M₀)]
    rw [← h1, hΓ, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective M₀)]
  by_contra hne
  have hnt : Nontrivial (Γ ⧸ M₀) := by
    refine ⟨⟨1, ?_⟩⟩
    obtain ⟨g, hg⟩ : ∃ g : Γ, g ∉ M₀ := by
      by_contra hcon
      push Not at hcon
      exact hne (Subgroup.eq_top_iff' _ |>.2 hcon)
    refine ⟨QuotientGroup.mk g, fun h => hg ((QuotientGroup.eq_one_iff g).1 h.symm)⟩
  have := IsSolvable.commutator_lt_top_of_nontrivial (Γ ⧸ M₀)
  rw [hperf] at this
  exact lt_irrefl _ this

theorem isSolvable_primeCore_three {X J : Subgroup G} (hJ : IsTwoPrimeComp X J)
    (h3 : 3 ∣ Nat.card ↥J) : Group.IsSolvable ↥(GLAPPrimeCore 3 ↥J) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq2 : CFSG.Open.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (quotEquivTwoImage hJ.1 hJ.2.1).symm hJ.2.2.2.2.2
  set Γ := ↥J
  set P : Subgroup Γ := CFSG.pCore 2 Γ with hP
  set Nn : Subgroup Γ := GLAPPrimeCore 3 Γ with hNn
  have hPN : P ≤ Nn := pCore_two_le_primeCore_three Γ
  have hNnTop : Nn ≠ ⊤ := by
    intro htop
    have hcop : Nat.Coprime 3 (Nat.card ↥Nn) := CFSG.pPrimeCore_coprime_card
    rw [htop, Subgroup.card_top] at hcop
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcop h3
  let q : Γ →* Γ ⧸ P := QuotientGroup.mk' P
  have hW : (Nn.map q) ≠ ⊤ := by
    intro htop
    apply hNnTop
    refine Subgroup.eq_top_iff' _ |>.2 fun g => ?_
    have : q g ∈ Nn.map q := by rw [htop]; exact Subgroup.mem_top _
    obtain ⟨n, hn, hng⟩ := this
    have : n⁻¹ * g ∈ P := (QuotientGroup.eq).1 hng
    have h2 : g = n * (n⁻¹ * g) := (mul_inv_cancel_left n g).symm
    rw [h2]
    exact Nn.mul_mem hn (hPN this)
  haveI : (Nn.map q).Normal :=
    (GLAPPrimeCore.normal 3 Γ).map q (QuotientGroup.mk'_surjective P)
  have hWc : Nn.map q ≤ Subgroup.center (Γ ⧸ P) := l119_normal_le_center hq2 hW
  let g₁ : ↥Nn →* ↥(Subgroup.center (Γ ⧸ P)) :=
    (q.comp Nn.subtype).codRestrict _ fun n => hWc ⟨n, n.2, rfl⟩
  haveI : Group.IsSolvable ↥(Subgroup.center (Γ ⧸ P)) := inferInstance
  haveI : Group.IsSolvable ↥g₁.ker := by
    have hkerP : ∀ n ∈ g₁.ker, ((n : Γ) ∈ P) := by
      intro n hn
      have h1 : q (n : Γ) = 1 := congrArg Subtype.val hn
      exact (QuotientGroup.eq_one_iff _).1 h1
    let φ : ↥g₁.ker →* ↥P :=
      (Nn.subtype.comp g₁.ker.subtype).codRestrict P fun n => hkerP n n.2
    have hφ : Function.Injective φ := by
      intro a b hab
      have h2 : ((a : ↥Nn) : Γ) = ((b : ↥Nn) : Γ) := congrArg (fun x : ↥P => (x : Γ)) hab
      exact Subtype.ext (Subtype.ext h2)
    have hp2 : IsPGroup 2 ↥g₁.ker :=
      (CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := Γ)).of_injective φ hφ
    haveI := hp2.isNilpotent
    infer_instance
  exact solvable_of_ker_le_range (g₁.ker).subtype g₁ (by simp [Subgroup.range_subtype])

theorem glaPComponent_of_twoPrimeComp {X Y J : Subgroup G} (hJ : IsTwoPrimeComp X J)
    (hXY : IsSubnormal X Y) (h3 : 3 ∣ Nat.card ↥J) : GLAPComponent 3 Y J := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJY : IsSubnormal J Y := isSubnormal_trans' hJ.2.1 hXY
  have hJle : J ≤ Y := isSubnormal_le' hJY
  have hqs := isQuasisimple_barOf_of_twoPrimeComp hJ h3
  have hsolv := isSolvable_primeCore_three hJ h3
  have hperf : commutator ↥J = ⊤ := Group.isPerfect_def.1 (Subgroup.isPerfect_iff.2 hJ.2.2.1)
  refine ⟨hJle, hJY, ⟨le_top, ?_, ?_⟩, ?_⟩
  · have := isSubnormal_barX (C := Y) 3 hJY
    rwa [barX_self] at this
  · exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (quotEquivBarX Nat.prime_three hJle hJY) hqs
  · intro J' hlt hJ'sn heq
    have hJ'J : IsSubnormal J' J := isSubnormal_of_le_of_le hJ'sn hlt.le hJle
    obtain ⟨M', hJ'M', hM'J, hM'ne, hM'n, -⟩ := isSubnormal_exists_normal hJ'J hlt.ne
    haveI := hM'n
    have hsplit : ∀ g : ↥J, ∃ m ∈ M'.subgroupOf J, ∃ n ∈ GLAPPrimeCore 3 ↥J, g = m * n := by
      intro g
      obtain ⟨j', hj', hjn⟩ := exists_of_barX_le (X := Y) (J := J') (K := J) (p := 3)
        (le_of_eq heq.symm) g.2 (hJle g.2)
      have hmem : j'⁻¹ * (g : G) ∈ J ⊓ GLAPPrimeCoreOf 3 Y :=
        ⟨J.mul_mem (J.inv_mem (hlt.le hj')) g.2, hjn⟩
      rw [glaPPrimeCoreOf_inf_eq_of_isSubnormal Nat.prime_three hJY] at hmem
      obtain ⟨n, hn, hng⟩ := hmem
      refine ⟨⟨j', hlt.le hj'⟩, (Subgroup.mem_subgroupOf).2 (hJ'M' hj'), n, hn, ?_⟩
      apply Subtype.ext
      have : (g : G) = j' * (j'⁻¹ * (g : G)) := by group
      rw [Subgroup.coe_mul]
      show (g : G) = j' * (n : G)
      rw [show (n : G) = j'⁻¹ * (g : G) from hng]
      exact this
    have htop := eq_top_of_perfect_of_solvable hperf (M₀ := M'.subgroupOf J) hsolv hsplit
    exact hM'ne (le_antisymm hM'J (Subgroup.subgroupOf_eq_top.1 htop))

theorem barX_ne_bot_of_three_dvd {Y J₀ : Subgroup G} (hJ₀Y : J₀ ≤ Y) (h3 : 3 ∣ Nat.card ↥J₀) :
    barX 3 Y J₀ ≠ ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hbot
  have hle : J₀ ≤ GLAPPrimeCoreOf 3 Y := by
    intro j hj
    have h1 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥Y) ⟨j, hJ₀Y hj⟩ ∈ barX 3 Y J₀ :=
      ⟨⟨j, hJ₀Y hj⟩, (Subgroup.mem_subgroupOf).2 hj, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    exact ⟨⟨j, hJ₀Y hj⟩, (QuotientGroup.eq_one_iff _).1 h1, rfl⟩
  exact not_dvd_card_glaPPrimeCoreOf Nat.prime_three Y (h3.trans (Subgroup.card_dvd_of_le hle))

theorem false_of_barX_comm {Y J₀ J : Subgroup G} (hJ₀Y : J₀ ≤ Y) (hJ₀J : J₀ ≤ J)
    (hperf : ⁅J₀, J₀⁆ = J₀) (h3 : 3 ∣ Nat.card ↥J₀)
    (hcomm : ∀ x ∈ barX 3 Y J, ∀ y ∈ barX 3 Y J₀, x * y = y * x) : False := by
  apply barX_ne_bot_of_three_dvd hJ₀Y h3
  have hB : ⁅barX 3 Y J₀, barX 3 Y J₀⁆ = barX 3 Y J₀ := barX_perfect 3 hJ₀Y hperf
  have hle : barX 3 Y J₀ ≤ barX 3 Y J := by
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨c, (Subgroup.mem_subgroupOf).2 (hJ₀J ((Subgroup.mem_subgroupOf).1 hc)), rfl⟩
  rw [eq_bot_iff, ← hB]
  refine Subgroup.commutator_le.2 fun x hx y hy => ?_
  have := hcomm x (hle hx) y hy
  rw [commutatorElement_def, this]
  simp

theorem glaPComponent_eq_of_common {Y J L J₀ : Subgroup G} (hJ : GLAPComponent 3 Y J)
    (hL : GLAPComponent 3 Y L) (hJ₀J : J₀ ≤ J) (hJ₀L : J₀ ≤ L) (hperf : ⁅J₀, J₀⁆ = J₀)
    (h3 : 3 ∣ Nat.card ↥J₀) : J = L := by
  by_contra hne
  have hbar : barX 3 Y J ≠ barX 3 Y L := fun h => hne (glaPComponent_unique hJ hL h)
  have hJ₀Y : J₀ ≤ Y := hJ₀J.trans hJ.1
  refine false_of_barX_comm hJ₀Y hJ₀J hperf h3 fun x hx y hy => ?_
  have hyL : y ∈ barX 3 Y L := by
    obtain ⟨c, hc, rfl⟩ := hy
    exact ⟨c, (Subgroup.mem_subgroupOf).2 (hJ₀L ((Subgroup.mem_subgroupOf).1 hc)), rfl⟩
  exact comp_comm hJ.2.2.1 hL.2.2.1 hbar hx hyL

theorem barX_biSup_le (p : ℕ) {Y : Subgroup G} {S : Set (Subgroup G)} (hS : ∀ L ∈ S, L ≤ Y) :
    barX p Y (⨆ L ∈ S, L) ≤ ⨆ L ∈ S, barX p Y L := by
  unfold barX
  have h1 : (⨆ L ∈ S, L).subgroupOf Y ≤ ⨆ L ∈ S, L.subgroupOf Y := by
    refine (subgroupOf_iSup_le (fun L : Subgroup G => ⨆ _ : L ∈ S, L)
      fun L => iSup_le fun hL => hS L hL).trans ?_
    refine iSup_mono fun L => ?_
    exact subgroupOf_iSup_le (fun _ : L ∈ S => L) fun hL => hS L hL
  refine (Subgroup.map_mono h1).trans ?_
  simp only [Subgroup.map_iSup]
  exact le_rfl

theorem barX_iSup_eq (p : ℕ) {Y : Subgroup G} {ι : Type*} (L : ι → Subgroup G) (hL : ∀ i, L i ≤ Y) :
    barX p Y (⨆ i, L i) = ⨆ i, barX p Y (L i) := by
  refine le_antisymm ?_ (iSup_le fun i => barX_mono (le_iSup L i))
  unfold barX
  refine (Subgroup.map_mono (subgroupOf_iSup_le L hL)).trans ?_
  rw [Subgroup.map_iSup]

theorem exists_glaPComponent_eq_of_family {Y J J₀ : Subgroup G} (hJ : GLAPComponent 3 Y J)
    {S : Set (Subgroup G)} (hS : ∀ L ∈ S, GLAPComponent 3 Y L) (hJ₀J : J₀ ≤ J)
    (hJ₀S : J₀ ≤ ⨆ L ∈ S, L) (hperf : ⁅J₀, J₀⁆ = J₀) (h3 : 3 ∣ Nat.card ↥J₀) :
    ∃ L ∈ S, J = L := by
  by_contra hcon
  push Not at hcon
  have hJ₀Y : J₀ ≤ Y := hJ₀J.trans hJ.1
  have hSY : ∀ L ∈ S, L ≤ Y := fun L hL => (hS L hL).1
  have hcent : ∀ L ∈ S, barX 3 Y L ≤
      Subgroup.centralizer (barX 3 Y J : Set (↥Y ⧸ GLAPPrimeCore 3 ↥Y)) := by
    intro L hLS y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hbar : barX 3 Y J ≠ barX 3 Y L := fun h =>
      hcon L hLS (glaPComponent_unique hJ (hS L hLS) h)
    exact comp_comm hJ.2.2.1 (hS L hLS).2.2.1 hbar hx hy
  have hjoin := barX_biSup_le 3 hSY
  have hSC : (⨆ L ∈ S, barX 3 Y L) ≤
      Subgroup.centralizer (barX 3 Y J : Set (↥Y ⧸ GLAPPrimeCore 3 ↥Y)) := iSup₂_le hcent
  refine false_of_barX_comm hJ₀Y hJ₀J hperf h3 fun x hx y hy => ?_
  have hyJS : y ∈ barX 3 Y (⨆ L ∈ S, L) := barX_mono hJ₀S hy
  have := hSC (hjoin hyJS)
  rw [Subgroup.mem_centralizer_iff] at this
  exact this x hx

end TP3

section Gen

variable {G : Type} [Group G] [Finite G]

@[expose] def Fam (p : ℕ) (C K : Subgroup G) (A0 : Subgroup ↥C) :
    Set (Subgroup (↥C ⧸ GLAPPrimeCore p ↥C)) :=
  {Z | ∃ z ∈ A0, Z = GLBConj (QuotientGroup.mk' (GLAPPrimeCore p ↥C) z) (barX p C K)}

theorem Fam_base (p : ℕ) (C K : Subgroup G) (A0 : Subgroup ↥C) :
    barX p C K ∈ Fam p C K A0 :=
  ⟨1, A0.one_mem, by rw [map_one, gLBConj_one]⟩

theorem Fam_comp {p : ℕ} {C K : Subgroup G} (hK : GLAPComponent p C K) (A0 : Subgroup ↥C) :
    ∀ Z ∈ Fam p C K A0, IsComponentOf Z ⊤ := by
  rintro Z ⟨z, -, rfl⟩
  exact l119_conj_component hK z

theorem Fam_bar_normalizes {p : ℕ} {C K : Subgroup G} (A0 : Subgroup ↥C) {y : ↥C} (hy : y ∈ A0) :
    QuotientGroup.mk' (GLAPPrimeCore p ↥C) y ∈
      Subgroup.normalizer ((sSup (Fam p C K A0) : Subgroup (↥C ⧸ GLAPPrimeCore p ↥C)) : Set _) := by
  set S : Subgroup (↥C ⧸ GLAPPrimeCore p ↥C) := sSup (Fam p C K A0) with hS
  have hstep : ∀ g : ↥C ⧸ GLAPPrimeCore p ↥C, (∃ w : ↥C, w ∈ A0 ∧ QuotientGroup.mk' (GLAPPrimeCore p ↥C) w = g) →
      S ≤ S.comap (MulAut.conj g).toMonoidHom := by
    rintro g ⟨w, hw, rfl⟩
    refine sSup_le fun Z hZ => ?_
    obtain ⟨z, hz, rfl⟩ := hZ
    intro x hx
    show (QuotientGroup.mk' (GLAPPrimeCore p ↥C) w) * x * (QuotientGroup.mk' (GLAPPrimeCore p ↥C) w)⁻¹ ∈ S
    have hmem : GLBConj (QuotientGroup.mk' (GLAPPrimeCore p ↥C) w⁻¹)
        (GLBConj (QuotientGroup.mk' (GLAPPrimeCore p ↥C) z) (barX p C K)) ∈ Fam p C K A0 :=
      ⟨z * w⁻¹, A0.mul_mem hz (A0.inv_mem hw), by
        rw [gLBConj_gLBConj, map_mul, map_inv]⟩
    have hsub : GLBConj (QuotientGroup.mk' (GLAPPrimeCore p ↥C) w⁻¹)
        (GLBConj (QuotientGroup.mk' (GLAPPrimeCore p ↥C) z) (barX p C K)) ≤ S :=
      le_sSup hmem
    apply hsub
    rw [mem_gLBConj]
    have hcancel : (QuotientGroup.mk' (GLAPPrimeCore p ↥C) w⁻¹) *
        ((QuotientGroup.mk' (GLAPPrimeCore p ↥C) w) * x * (QuotientGroup.mk' (GLAPPrimeCore p ↥C) w)⁻¹) *
        (QuotientGroup.mk' (GLAPPrimeCore p ↥C) w⁻¹)⁻¹ = x := by
      rw [map_inv]
      group
    rw [hcancel]
    exact hx
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact hstep _ ⟨y, hy, rfl⟩ hh
  · intro hh
    have hh' := hstep (QuotientGroup.mk' (GLAPPrimeCore p ↥C) y⁻¹) ⟨y⁻¹, A0.inv_mem hy, rfl⟩ hh
    have e : (QuotientGroup.mk' (GLAPPrimeCore p ↥C) y⁻¹) *
        ((QuotientGroup.mk' (GLAPPrimeCore p ↥C) y) * h * (QuotientGroup.mk' (GLAPPrimeCore p ↥C) y)⁻¹) *
        (QuotientGroup.mk' (GLAPPrimeCore p ↥C) y⁻¹)⁻¹ = h := by
      rw [map_inv]
      group
    have hh'' : (QuotientGroup.mk' (GLAPPrimeCore p ↥C) y⁻¹) *
        ((QuotientGroup.mk' (GLAPPrimeCore p ↥C) y) * h * (QuotientGroup.mk' (GLAPPrimeCore p ↥C) y)⁻¹) *
        (QuotientGroup.mk' (GLAPPrimeCore p ↥C) y⁻¹)⁻¹ ∈ S := hh'
    rw [e] at hh''
    exact hh''

theorem layer_le_gen {p : ℕ} (hp : p.Prime) (Ty : ∀ (X : Type) [Group X], Prop)
    (hTyiso : ∀ (X Y : Type) [Group X] [Group Y], (X ≃* Y) → Ty X → Ty Y)
    (hnb : ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsQuasisimple X →
      Ty (X ⧸ Subgroup.center X) → ¬ IsLocallyOTwoBalancedWrtP p 1 X ∧ ¬ IsLTwoTwentySeven X)
    {m : ℕ} {B M E A : Subgroup G} {a : G}
    (hSec : Sec11 G m p B M E A) (ha : a ∈ A) (ha1 : a ≠ 1)
    (hnotD : ¬ ∃ A1 : Subgroup G, inD p M A1 ∧ a ∈ A1) (h115 : Prop115Statement)
    {b : G} (hbA0 : b ∈ E ⊓ A) (hb1 : b ≠ 1) (hbC : b ∈ Cg a)
    (hbp : IsPGroup p (Subgroup.zpowers b))
    {L : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a))} (hL : IsSubnormal L ⊤)
    {Q : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a))}
    (hQ : GLAPComponent p (L ⊓ Subgroup.centralizer
      ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) ⟨b, hbC⟩} :
        Set (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)))) Q)
    (hQty : Ty ((↥Q ⧸ GLAPPrimeCore p ↥Q) ⧸ Subgroup.center (↥Q ⧸ GLAPPrimeCore p ↥Q))) :
    Q ≤ barX p (Cg a) M := by
  obtain ⟨P, hP, hPQ, ⟨e⟩⟩ := l119_layer_piece hp hbC hbp hL hQ
  have hPq : CFSG.Open.IsQuasisimple (↥P ⧸ GLAPPrimeCore p ↥P) := l119_isQuasisimple_barOf hp hP
  have hTP : Ty ((↥P ⧸ GLAPPrimeCore p ↥P) ⧸ Subgroup.center (↥P ⧸ GLAPPrimeCore p ↥P)) :=
    hTyiso _ _ e hQty
  obtain ⟨h1', h27⟩ := hnb _ hPq hTP
  have h1 : ¬ IsLocallyOTwoBalancedWrtP p 1 (barOf p P) := h1'
  have h2 : p = 3 → IsLTwoTwentySeven (barOf p P) → ¬ IsCompLocallyOTwoBalanced p 1 A P :=
    fun _ hL27 _ => h27 hL27
  have hJ : GLAPComponent p (Cg2 b a) P := by
    unfold Cg2
    rw [l119_cg2_eq]
    exact hP
  rcases h115 hSec ha ha1 hbA0 hb1 hJ h1 h2 with hPM | ⟨A1, hA1, haA1⟩
  · rw [← hPQ]
    exact barX_mono hPM
  · exact absurd ⟨A1, hA1, haA1⟩ hnotD

theorem no_bad_gen {p : ℕ} (hp : p.Prime) (Ty : ∀ (X : Type) [Group X], Prop)
    (hTyiso : ∀ (X Y : Type) [Group X] [Group Y], (X ≃* Y) → Ty X → Ty Y)
    (hnb : ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsQuasisimple X →
      Ty (X ⧸ Subgroup.center X) → ¬ IsLocallyOTwoBalancedWrtP p 1 X ∧ ¬ IsLTwoTwentySeven X)
    {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G}
    (hSec : Sec11 G m p B M E A) (ha : a ∈ A) (ha1 : a ≠ 1)
    (hK : GLAPComponent p (Cg a) K) (hKM : ¬ K ≤ M) (hpK : p ∣ Nat.card ↥(barX p (Cg a) K))
    (hnotD : ¬ ∃ A1 : Subgroup G, inD p M A1 ∧ a ∈ A1)
    (hKTy : Ty ((↥K ⧸ GLAPPrimeCore p ↥K) ⧸ Subgroup.center (↥K ⧸ GLAPPrimeCore p ↥K)))
    (h111 : Prop111Statement) (hI22 : Input22_3_2) (hI18 : Input18_3_diag)
    (h115 : Prop115Statement) :
    ¬ ∃ z : ↥(Cg a), (z : G) ∈ E ⊓ A ∧ (z : G) ≠ 1 ∧
      ((z : G) ∉ Subgroup.normalizer (K : Set G) ∨
        ∀ q ∈ barX p (Cg a) K, QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z * q =
          q * QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  rintro ⟨z₀, hz₀A, hz₀1, hbad⟩
  obtain ⟨hDDp, -⟩ := hSec.pair
  obtain ⟨-, hDp, hrA0⟩ := hDDp
  obtain ⟨hSCs, -⟩ := hDp
  obtain ⟨hSCp, -⟩ := hSCs
  obtain ⟨-, hAel, -⟩ := hSCp
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hApow : ∀ x ∈ A, x ^ p = 1 := fun x hx => hAel.2 x hx
  have hACg : A ≤ Cg a := fun x hx => by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact hAcomm a ha x hx
  set A0 : Subgroup G := E ⊓ A with hA0
  have hA0A : A0 ≤ A := inf_le_right
  have hA0C : A0 ≤ Cg a := hA0A.trans hACg
  have hA0el : IsElemAbelian p A0 := l119_isElemAbelian_of_le hA0A hAel
  have hrA0 : 2 ≤ CFSG.Open.pRank p A0 := hrA0
  set A0C : Subgroup ↥(Cg a) := A0.subgroupOf (Cg a) with hA0Cdef
  set Bbar : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)) :=
    A0C.map (QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a))) with hBbar
  set Kb : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)) := barX p (Cg a) K with hKb
  set 𝓛 := Fam p (Cg a) K A0C with h𝓛def
  set Yb : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)) := sSup 𝓛 with hYb
  have hKbc : IsComponentOf Kb ⊤ := l119_isComponent_barX hK
  have hKbmem : Kb ∈ 𝓛 := Fam_base p (Cg a) K A0C
  have h𝓛c : ∀ X ∈ 𝓛, IsComponentOf X ⊤ := Fam_comp hK A0C
  have hcomm𝓛 : ∀ X ∈ 𝓛, ∀ X' ∈ 𝓛, X ≠ X' → ∀ x ∈ X, ∀ y ∈ X', x * y = y * x := by
    rintro X ⟨w, -, rfl⟩ X' ⟨w', -, rfl⟩ hne x hx y hy
    exact l119_conj_comm hK hne hx hy
  have hYsub : IsSubnormal Yb ⊤ := l119_isSubnormal_sSup_components h𝓛c
  have hYcomp : ∀ X ∈ 𝓛, IsComponentOf X Yb := fun X hX => l119_isComponentOf_sSup h𝓛c hcomm𝓛 hX
  have hBcomm : ∀ z ∈ A0C, ∀ w ∈ A0C,
      QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z * QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) w =
        QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) w * QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z := by
    intro z hz w hw
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hAcomm _ (hA0A ((Subgroup.mem_subgroupOf).1 hz)) _ (hA0A ((Subgroup.mem_subgroupOf).1 hw))
  have hBnorm : Bbar ≤ Subgroup.normalizer ((Yb : Subgroup _) : Set _) := by
    rintro _ ⟨z, hz, rfl⟩
    exact Fam_bar_normalizes A0C hz
  have hA0Cel : IsElemAbelian p A0C := l119_isElemAbelian_subgroupOf hA0el (Cg a)
  have hBel : IsElemAbelian p Bbar :=
    CFSG.SectionRank.isElemAbelian_map hA0Cel _
  have hB_rank : 2 ≤ CFSG.Open.pRank p Bbar := le_trans hrA0 (l119_pRank_image_ge hp hA0C hA0el)
  have hKbe : (↥K ⧸ GLAPPrimeCore p ↥K) ≃* ↥Kb := quotEquivBarX hp hK.1 hK.2.1
  have hKbT' : Ty (↥Kb ⧸ Subgroup.center ↥Kb) :=
    hTyiso _ _ (l119_centerQuot_equiv hKbe) hKTy
  have hpY : p ∣ Nat.card ↥Yb :=
    dvd_trans hpK (Subgroup.card_dvd_of_le (le_sSup hKbmem))
  have htrans : ∀ X ∈ 𝓛, ∀ X' ∈ 𝓛, ∃ b ∈ Bbar, GLBConj b X = X' := by
    rintro X ⟨w, hw, rfl⟩ X' ⟨w', hw', rfl⟩
    exact ⟨QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) (w⁻¹ * w'),
      Subgroup.mem_map_of_mem _ (A0C.mul_mem (A0C.inv_mem hw) hw'), l119_conj_trans w w'⟩
  have hz₀C : z₀ ∈ A0C := Subgroup.mem_subgroupOf.2 hz₀A
  have hb₀B : QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z₀ ∈ Bbar :=
    Subgroup.mem_map_of_mem _ hz₀C
  have hz₀pow : z₀ ^ p = 1 := by
    apply Subtype.ext
    simpa using hApow _ hz₀A.2
  have hb₀1 : QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z₀ ≠ 1 := by
    intro h
    apply hz₀1
    have h2 := l119_eq_one_of_pow_of_mem_core hp hz₀pow ((QuotientGroup.eq_one_iff _).1 h)
    simpa using congrArg Subtype.val h2
  have hJb₀ : QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z₀ ∈ Subgroup.centralizer (Yb : Set _) ∨
      QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z₀ ∉ Subgroup.normalizer (Kb : Set _) := by
    rcases hbad with hN | hC
    · right
      intro hb
      exact hN (l119_mem_normalizer_of_bar hp hK z₀ hb)
    · left
      have hYc : Yb ≤ Subgroup.centralizer
          ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z₀} : Set _) := by
        refine sSup_le fun X hX => ?_
        obtain ⟨w, hw, rfl⟩ := hX
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        rw [Set.mem_singleton_iff] at hg
        rw [hg]
        exact l119_centralizes_gLBConj (hBcomm z₀ hz₀C w hw) hC x hx
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have h2 := hYc hh
      rw [Subgroup.mem_centralizer_iff] at h2
      exact (h2 _ (Set.mem_singleton _)).symm
  have hLayer : ∀ b ∈ Bbar, b ≠ 1 → (b ∈ Subgroup.centralizer (Yb : Set _) ∨
      b ∉ Subgroup.normalizer (Kb : Set _)) →
      GLAPLayer p (Yb ⊓ Subgroup.centralizer ({b} : Set _)) ≤ barX p (Cg a) M := by
    intro b hb hb1 hJ
    have hbB := hb
    obtain ⟨z, hz, rfl⟩ := hb
    have hzA : (z : G) ∈ A0 := Subgroup.mem_subgroupOf.1 hz
    have hz1 : (z : G) ≠ 1 := by
      intro h
      apply hb1
      have hzeq : z = 1 := Subtype.ext h
      rw [hzeq, map_one]
    have hzpow : (z : G) ^ p = 1 := hApow _ hzA.2
    have hzC : (z : G) ∈ Cg a := z.2
    have hzp : IsPGroup p (Subgroup.zpowers (z : G)) := l119_isPGroup_zpowers hzpow
    have hzpow' : z ^ p = 1 := by
      apply Subtype.ext
      simpa using hzpow
    have hbord : orderOf (QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z) = p := by
      apply orderOf_eq_prime
      · rw [← map_pow, hzpow', map_one]
      · exact hb1
    have hdich : QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z ∈ Subgroup.centralizer (Yb : Set _) ∨
        ∀ X ∈ 𝓛, QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z ∉ Subgroup.normalizer (X : Set _) := by
      rcases hJ with hC | hN
      · left
        exact hC
      · right
        rintro X ⟨w, hw, rfl⟩ hmem
        apply hN
        exact (l119_normalizer_gLBConj_iff (hBcomm z hz w hw) Kb).1 hmem
    unfold GLAPLayer
    refine sSup_le fun Q hQ => ?_
    obtain ⟨X₀, hX₀, ⟨e0⟩⟩ := hI18 (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)) p hp Yb 𝓛
      (QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z) hbord (hBnorm hbB) rfl hYcomp hcomm𝓛 hdich Q hQ
    obtain ⟨w, hw, rfl⟩ := hX₀
    have eK : ↥(GLBConj (QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) w) Kb) ≃* ↥Kb :=
      (l119_gLBConj_equiv _ Kb).symm
    have hQK : Nonempty ((↥Q ⧸ GLAPPrimeCore p ↥Q) ⧸ Subgroup.center (↥Q ⧸ GLAPPrimeCore p ↥Q) ≃*
        ↥Kb ⧸ Subgroup.center ↥Kb) := ⟨e0.trans (l119_centerQuot_equiv eK)⟩
    exact layer_le_gen hp Ty hTyiso hnb hSec ha ha1 hnotD h115 hzA hz1 hzC hzp hYsub hQ
      (hTyiso _ _ hQK.some.symm hKbT')
  have hYM : Yb ≤ barX p (Cg a) M := by
    have hI22' := hI22 (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)) p hp Bbar Yb Kb 𝓛 hBel hBnorm
      hKbmem hB_rank hpY rfl hYcomp hcomm𝓛 htrans
      ⟨QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z₀, hb₀B, hb₀1, hJb₀⟩
    rw [hI22']
    refine sSup_le ?_
    rintro Z ⟨b, hb, hb1, hJ, rfl⟩
    exact hLayer b hb hb1 hJ
  have hKM' : barX p (Cg a) K ≤ barX p (Cg a) M := le_trans (le_sSup hKbmem) hYM
  apply hKM
  intro k hk
  obtain ⟨m, hm, hmk⟩ := exists_of_barX_le hKM' hk (hK.1 hk)
  have hmM : m⁻¹ * k ∈ M := h111 hSec ha ha1 hmk
  have := M.mul_mem hm hmM
  simpa using this

end Gen

section Transport

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def barCongr {X Y : Type*} [Group X] [Group Y] (p : ℕ) (e : X ≃* Y) :
    (X ⧸ GLAPPrimeCore p X) ≃* (Y ⧸ GLAPPrimeCore p Y) :=
  QuotientGroup.congr _ _ e (glaPPrimeCore_map_iso p e)

theorem glaPComponent_subgroupOf {p : ℕ} (hp : p.Prime) {A K Y : Subgroup G}
    (hAY : A ≤ Y) (hK : GLAPComponent p A K) :
    GLAPComponent p (A.subgroupOf Y) (K.subgroupOf Y) := by
  have hker : Nat.Coprime p (Nat.card ↥(A.subgroupOf Y ⊓ Y.subtype.ker)) := by
    rw [Subgroup.ker_subtype, inf_bot_eq, Subgroup.card_bot]
    exact Nat.coprime_one_right p
  have hK' : GLAPComponent p ((A.subgroupOf Y).map Y.subtype) K := by
    rw [Subgroup.map_subgroupOf_eq_of_le hAY]
    exact hK
  obtain ⟨K₀, hK₀, hK₀map⟩ := exists_glaPComponent_map_eq hp Y.subtype hker hK'
  have hsub : (K₀.map Y.subtype).subgroupOf Y = K₀ :=
    Subgroup.comap_map_eq_self_of_injective Y.subtype_injective K₀
  rw [hK₀map] at hsub
  rw [hsub]
  exact hK₀

theorem glaPComponent_barX_inf_centralizer {p : ℕ} (hp : p.Prime) {M L K : Subgroup G} {d : G}
    (hdM : d ∈ M) (hLM : L ≤ M) (hdL : d ∈ Subgroup.normalizer (L : Set G))
    (hd : IsPGroup p (Subgroup.zpowers d))
    (hK : GLAPComponent p (L ⊓ Subgroup.centralizer ({d} : Set G)) K) :
    GLAPComponent p (barX p M L ⊓ Subgroup.centralizer
      ({QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨d, hdM⟩} : Set (↥M ⧸ GLAPPrimeCore p ↥M)))
      (barX p M K) := by
  have : Fact p.Prime := ⟨hp⟩
  set A : Subgroup G := L ⊓ Subgroup.centralizer ({d} : Set G) with hA
  have hAM : A ≤ M := inf_le_left.trans hLM
  set ψ : ↥M →* ↥M ⧸ GLAPPrimeCore p ↥M := QuotientGroup.mk' (GLAPPrimeCore p ↥M) with hψ
  have hker : Nat.Coprime p (Nat.card ↥((A.subgroupOf M) ⊓ ψ.ker)) := by
    rw [hψ, QuotientGroup.ker_mk']
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
      CFSG.pPrimeCore_coprime_card
  have hmap : (A.subgroupOf M).map ψ = barX p M L ⊓ Subgroup.centralizer
      ({QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨d, hdM⟩} : Set (↥M ⧸ GLAPPrimeCore p ↥M)) :=
    barX_inf_centralizer hp hdM hLM hdL hd
  have h1 := glaPComponent_map hp ψ hker (glaPComponent_subgroupOf hp hAM hK)
  rw [hmap] at h1
  exact h1

@[expose] noncomputable def barOfBarX {p : ℕ} (hp : p.Prime) {M K : Subgroup G} (hKM : K ≤ M) :
    (↥K ⧸ GLAPPrimeCore p ↥K) ≃*
      (↥(barX p M K) ⧸ GLAPPrimeCore p ↥(barX p M K)) := by
  have hker : Nat.Coprime p (Nat.card ↥((K.subgroupOf M) ⊓ (QuotientGroup.mk' (GLAPPrimeCore p ↥M)).ker)) := by
    rw [QuotientGroup.ker_mk']
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
      (haveI : Fact p.Prime := ⟨hp⟩; CFSG.pPrimeCore_coprime_card)
  exact (barCongr p (Subgroup.subgroupOfEquivOfLe hKM)).symm.trans
    (lcEquiv hp (QuotientGroup.mk' (GLAPPrimeCore p ↥M)) (K.subgroupOf M) hker)

theorem primeCoreOf_top_eq_bot {p : ℕ} {Y : Type} [Group Y] [Finite Y]
    (hY : GLAPPrimeCore p Y = ⊥) : GLAPPrimeCoreOf p (⊤ : Subgroup Y) = ⊥ := by
  have hiso := glaPPrimeCore_map_iso p (Subgroup.topEquiv : ↥(⊤ : Subgroup Y) ≃* Y)
  rw [hY] at hiso
  have h1 : GLAPPrimeCore p ↥(⊤ : Subgroup Y) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hm : (Subgroup.topEquiv : ↥(⊤ : Subgroup Y) ≃* Y) x ∈
        (GLAPPrimeCore p ↥(⊤ : Subgroup Y)).map
          (Subgroup.topEquiv : ↥(⊤ : Subgroup Y) ≃* Y).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hx
    rw [hiso, Subgroup.mem_bot] at hm
    rw [Subgroup.mem_bot]
    exact (Subgroup.topEquiv : ↥(⊤ : Subgroup Y) ≃* Y).injective (hm.trans (map_one _).symm)
  unfold GLAPPrimeCoreOf
  rw [h1, Subgroup.map_bot]

theorem primeCore_sub_eq_bot {p : ℕ} (hp : p.Prime) {Y : Type} [Group Y] [Finite Y]
    (hY : GLAPPrimeCore p Y = ⊥) {S : Subgroup Y} (hS : IsSubnormal S ⊤) :
    GLAPPrimeCore p ↥S = ⊥ := by
  have h1 : GLAPPrimeCoreOf p S ≤ GLAPPrimeCoreOf p (⊤ : Subgroup Y) :=
    glaPPrimeCoreOf_le_of_isSubnormal hp hS
  rw [primeCoreOf_top_eq_bot hY] at h1
  rw [eq_bot_iff]
  intro x hx
  have hm : (x : Y) ∈ GLAPPrimeCoreOf p S := Subgroup.mem_map_of_mem S.subtype hx
  have := h1 hm
  rw [Subgroup.mem_bot] at this ⊢
  exact Subtype.ext this

end Transport

section Pumpup

variable {G : Type} [Group G] [Finite G]

abbrev bar3 (a : G) (z : G) (hz : z ∈ Cg a) : ↥(Cg a) ⧸ GLAPPrimeCore 3 ↥(Cg a) :=
  QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cg a)) ⟨z, hz⟩

theorem pumpup_type (hI : Prop126.Input14_15_3) (hkp : CFSG.Open.IsKProper G)
    {a z : G} (hC : Cg a ≠ ⊤) (hzC : z ∈ Cg a) (hz3 : z ^ 3 = 1)
    {L J₀ : Subgroup G} (hL : GLAPComponent 3 (Cg a) L)
    (hzL : z ∈ Subgroup.normalizer (L : Set G))
    (hJ₀ : GLAPComponent 3 (L ⊓ Cg z) J₀)
    (hJty : IsAltType 7 (barOf 3 J₀) ∨ IsHatSeven (barOf 3 J₀))
    (hnc : ∃ q ∈ barX 3 (Cg a) L, bar3 a z hzC * q ≠ q * bar3 a z hzC) :
    IsSporType .He (↥(barX 3 (Cg a) L) ⧸ Subgroup.center ↥(barX 3 (Cg a) L)) ∨
      ∃ k : ℕ, 1 ≤ k ∧
        IsAltType (7 + 3 * k) (↥(barX 3 (Cg a) L) ⧸ Subgroup.center ↥(barX 3 (Cg a) L)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKbc : IsComponentOf (barX 3 (Cg a) L) ⊤ := hL.2.2.1
  have hKq : CFSG.Open.IsQuasisimple ↥(barX 3 (Cg a) L) := hKbc.2.2
  have hKG : CFSG.Open.IsKGroup ↥(barX 3 (Cg a) L) :=
    ((isKGroup_of_isKProper hkp hC).quotient _).subgroup _
  have hcore : GLAPPrimeCore 3 ↥(barX 3 (Cg a) L) = ⊥ :=
    primeCore_sub_eq_bot Nat.prime_three (glaPPrimeCore_quotient_eq_bot Nat.prime_three) hKbc.2.1
  have hLC : L ≤ Cg a := hL.1
  have hzN : bar3 a z hzC ∈ Subgroup.normalizer ((barX 3 (Cg a) L : Subgroup _) : Set _) := by
    have h1 := l119_barX_gLBConj (p := 3) (C := Cg a) (H := L) hzC hLC
    rw [mem_normalizer_iff_gLBConj_eq.1 hzL] at h1
    exact mem_normalizer_iff_gLBConj_eq.2 h1.symm
  let x : MulAut ↥(barX 3 (Cg a) L) :=
    (barX 3 (Cg a) L).normalizerMonoidHom ⟨bar3 a z hzC, hzN⟩
  have hxk : ∀ k : ↥(barX 3 (Cg a) L), ((x k : ↥(barX 3 (Cg a) L)) : _) =
      bar3 a z hzC * (k : _) * (bar3 a z hzC)⁻¹ := fun k =>
    (barX 3 (Cg a) L).normalizerMonoidHom_apply_apply_coe ⟨bar3 a z hzC, hzN⟩ k
  have hfix : Prop126.autFixSub x = ((barX 3 (Cg a) L) ⊓ Subgroup.centralizer
      ({bar3 a z hzC} : Set (↥(Cg a) ⧸ GLAPPrimeCore 3 ↥(Cg a)))).subgroupOf (barX 3 (Cg a) L) := by
    ext k
    show x k = k ↔ _
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      refine ⟨k.2, ?_⟩
      have := congrArg Subtype.val h
      rw [hxk] at this
      calc (k : _) * bar3 a z hzC = (bar3 a z hzC * (k : _) * (bar3 a z hzC)⁻¹) * bar3 a z hzC := by
            rw [this]
        _ = bar3 a z hzC * (k : _) := by group
    · rintro ⟨-, h⟩
      apply Subtype.ext
      rw [hxk]
      calc bar3 a z hzC * (k : _) * (bar3 a z hzC)⁻¹ = (k : _) * bar3 a z hzC * (bar3 a z hzC)⁻¹ := by
            rw [h]
        _ = k := by group
  have hxord : orderOf x = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · ext k
      have h3 : bar3 a z hzC ^ 3 = 1 := by
        rw [← map_pow]
        have : (⟨z, hzC⟩ : ↥(Cg a)) ^ 3 = 1 := Subtype.ext (by simpa using hz3)
        rw [this, map_one]
      have hx3 : x ^ 3 = (barX 3 (Cg a) L).normalizerMonoidHom
          (⟨bar3 a z hzC, hzN⟩ ^ 3) := by rw [map_pow]
      have h13 : (⟨bar3 a z hzC, hzN⟩ :
          ↥(Subgroup.normalizer ((barX 3 (Cg a) L : Subgroup _) : Set _))) ^ 3 = 1 :=
        Subtype.ext (by simpa using h3)
      rw [hx3, h13, map_one]
    · intro hx1
      obtain ⟨q, hq, hqne⟩ := hnc
      apply hqne
      have := congrArg Subtype.val (DFunLike.congr_fun hx1 ⟨q, hq⟩)
      rw [hxk] at this
      calc bar3 a z hzC * q = (bar3 a z hzC * q * (bar3 a z hzC)⁻¹) * bar3 a z hzC := by group
        _ = q * bar3 a z hzC := by
          have h' : bar3 a z hzC * q * (bar3 a z hzC)⁻¹ = q := this
          rw [h']
  have hJ₁ : GLAPComponent 3 (Prop126.autFixSub x)
      ((barX 3 (Cg a) J₀).subgroupOf (barX 3 (Cg a) L)) := by
    have hd : IsPGroup 3 (Subgroup.zpowers z) := l119_isPGroup_zpowers hz3
    have h1 := glaPComponent_barX_inf_centralizer (p := 3) Nat.prime_three (M := Cg a) hzC hLC hzL hd hJ₀
    rw [hfix]
    exact glaPComponent_subgroupOf Nat.prime_three inf_le_left h1
  have hJ₀C : J₀ ≤ Cg a := hJ₀.1.trans (inf_le_left.trans hLC)
  have hJ₁le : barX 3 (Cg a) J₀ ≤ barX 3 (Cg a) L := barX_mono (hJ₀.1.trans inf_le_left)
  have e : (↥J₀ ⧸ GLAPPrimeCore 3 ↥J₀) ≃*
      (↥((barX 3 (Cg a) J₀).subgroupOf (barX 3 (Cg a) L)) ⧸
        GLAPPrimeCore 3 ↥((barX 3 (Cg a) J₀).subgroupOf (barX 3 (Cg a) L))) :=
    (barOfBarX Nat.prime_three hJ₀C).trans
      (barCongr 3 (Subgroup.subgroupOfEquivOfLe hJ₁le)).symm
  have hJ₁ty : IsAltType 7 (barOf 3 ((barX 3 (Cg a) J₀).subgroupOf (barX 3 (Cg a) L))) ∨
      IsHatSeven (barOf 3 ((barX 3 (Cg a) J₀).subgroupOf (barX 3 (Cg a) L))) := by
    rcases hJty with h | h
    · exact Or.inl (l119_isAltType_congr 7 e h)
    · exact Or.inr (IsHatSeven.of_mulEquiv e h)
  exact hI ↥(barX 3 (Cg a) L) hKq hKG hcore x hxord _ hJ₁ hJ₁ty

end Pumpup

section Inputs

abbrev barZ3 {Y : Type} [Group Y] (Q : Subgroup Y) : Type :=
  (↥Q ⧸ GLAPPrimeCore 3 ↥Q) ⧸ Subgroup.center (↥Q ⧸ GLAPPrimeCore 3 ↥Q)

@[expose] def NotL227 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsLTwoTwentySeven X →
    (∀ n : ℕ, 5 ≤ n → ¬ IsAltType n (X ⧸ Subgroup.center X)) ∧
      ¬ IsSporType .He (X ⧸ Subgroup.center X) ∧ ¬ IsLpType 2 7 (X ⧸ Subgroup.center X)

@[expose] def InputAltCentre : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 8 ≤ n → CFSG.Open.IsQuasisimple X →
    GLAPPrimeCore 3 X = ⊥ → IsAltType n (X ⧸ Subgroup.center X) → IsAltType n X

@[expose] def InputHeCent : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y), CFSG.Open.IsQuasisimple ↥K →
    IsSporType .He (↥K ⧸ Subgroup.center ↥K) → ∀ b : Y, b ∈ Subgroup.normalizer (K : Set Y) →
      orderOf b = 3 → (∃ q ∈ K, b * q ≠ q * b) →
        ∀ Q : Subgroup Y, GLAPComponent 3 (K ⊓ Subgroup.centralizer ({b} : Set Y)) Q →
          IsLpType 2 7 (barZ3 Q) ∨ IsAltType 7 (barZ3 Q)

@[expose] def InputHeGen : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K B : Subgroup Y), CFSG.Open.IsQuasisimple ↥K →
    IsSporType .He (↥K ⧸ Subgroup.center ↥K) → B ≤ Subgroup.normalizer (K : Set Y) →
      IsElemAbelian 3 B → 2 ≤ CFSG.Open.pRank 3 B → (∀ b ∈ B, b ≠ 1 → ∃ q ∈ K, b * q ≠ q * b) →
        K ≤ ⨆ (b : Y) (_ : b ∈ B) (_ : b ≠ 1), GLAPLayer 3 (K ⊓ Subgroup.centralizer ({b} : Set Y))

@[expose] def InputAnCent : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y) (n : ℕ), 8 ≤ n → n % 3 = 1 →
    CFSG.Open.IsQuasisimple ↥K → IsAltType n (↥K ⧸ Subgroup.center ↥K) →
    ∀ b : Y, b ∈ Subgroup.normalizer (K : Set Y) → orderOf b = 3 → (∃ q ∈ K, b * q ≠ q * b) →
      ∀ Q : Subgroup Y, GLAPComponent 3 (K ⊓ Subgroup.centralizer ({b} : Set Y)) Q →
        ∃ r : ℕ, 5 ≤ r ∧ r % 3 = 1 ∧ IsAltType r (barZ3 Q)

@[expose] def Input23_7_amb : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K B : Subgroup Y) (n : ℕ), 8 ≤ n → n % 3 = 1 →
    IsAltType n ↥K → B ≤ Subgroup.normalizer (K : Set Y) → IsElemAbelian 3 B →
    (∀ b ∈ B, b ≠ 1 → ∃ q ∈ K, b * q ≠ q * b) →
    ∀ a ∈ B, a ≠ 1 → ∀ J : Subgroup Y,
      GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set Y)) J →
      IsAltType 7 (barZ3 J) →
      ∀ W : Subgroup Y, W = ⨆ (b : Y) (_ : b ∈ B) (_ : b ≠ 1),
        (GLAPPrimeCoreOf 3 (K ⊓ Subgroup.centralizer ({b} : Set Y)) ⊔
          GLAPLayer 3 (K ⊓ Subgroup.centralizer ({b} : Set Y))) →
      ∀ I : Subgroup Y, I = ⨆ w ∈ W, GLBConj w J →
      (∃ (ι : Type) (Q : ι → Subgroup (↥I ⧸ CFSG.pCore 2 ↥I)),
        (∀ i, IsAltType 7 ↥(Q i) ∨ IsHatSeven ↥(Q i)) ∧
        (∀ i j, i ≠ j → ∀ x ∈ Q i, ∀ y ∈ Q j, x * y = y * x) ∧ (⨆ i, Q i) = ⊤) →
      3 ^ CFSG.Open.pRank 3 B ∣ n - 7

@[expose] def Setup126 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m : ℕ} {B M E A : Subgroup G} (_ : Sec11 G m 3 B M E A) {a : G}
    (_ : a ∈ A) (_ : a ≠ 1) (_ : ∀ A₁ : Subgroup G, inD 3 M A₁ → a ∉ A₁)
    {J : Subgroup G} (_ : IsTwoPrimeComp (alphaOf 3 M ⊓ Cg a) J)
    {R : Subgroup G} (_ : IsSylowIn 3 M R) (_ : E ⊔ A ≤ R) {z : G} (_ : z ∈ centerOf R)
    (_ : z ∈ alphaOf 3 M) (_ : orderOf z = 3),
    ∃ J₀ : Subgroup G, GLAPComponent 3 (Cg2 z a) J₀ ∧ J₀ ≤ J ∧
      (∀ j ∈ J, ∃ j₀ ∈ J₀, j₀⁻¹ * j ∈ pCoreOf 2 J) ∧
      (IsAltType 7 (↥J ⧸ CFSG.pCore 2 ↥J) ∨ IsHatSeven (↥J ⧸ CFSG.pCore 2 ↥J)) ∧
      (IsAltType 7 (barOf 3 J₀) ∨ IsHatSeven (barOf 3 J₀))

structure Sib126 : Prop where
  h111 : Prop111Statement
  h112 : Prop112Statement
  h115 : Prop115Statement
  h117 : Prop117_cex_falseStatement
  h121 : Prop121_of_cexStatement

end Inputs

section Types

theorem card_alt' (m : ℕ) (hm : 2 ≤ m) :
    Nat.card (alternatingGroup (Fin m)) = m.factorial / 2 := by
  haveI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem three_dvd_of_isAltType_seven {X : Type} [Group X] [Finite X] (h : IsAltType 7 X) :
    3 ∣ Nat.card X := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, card_alt' 7 (by norm_num)]
  decide

theorem three_dvd_of_isHatSeven {X : Type} [Group X] [Finite X] (h : IsHatSeven X) :
    3 ∣ Nat.card X := by
  have h1 : Nat.card (Subgroup.center X) ∣ Nat.card X := Subgroup.card_subgroup_dvd_card _
  rw [h.2.1] at h1
  exact h1

theorem three_dvd_of_ty7 {X : Type} [Group X] [Finite X] (h : IsAltType 7 X ∨ IsHatSeven X) :
    3 ∣ Nat.card X :=
  h.elim three_dvd_of_isAltType_seven three_dvd_of_isHatSeven

theorem alt7_noncomm : ∃ x y : ↥(alternatingGroup (Fin 7)), x * y ≠ y * x := by
  refine ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.Perm.mem_alternatingGroup.2 (by decide)⟩,
    ⟨Equiv.swap 2 3 * Equiv.swap 3 4, Equiv.Perm.mem_alternatingGroup.2 (by decide)⟩, ?_⟩
  intro h
  have := congrArg Subtype.val h
  revert this
  decide

theorem center_eq_bot_of_isAltType_seven {X : Type} [Group X] (h : IsAltType 7 X) :
    Subgroup.center X = ⊥ := by
  obtain ⟨e⟩ := h
  haveI : IsSimpleGroup X := e.isSimpleGroup_congr.2 S7.isSimple_Alt7
  rcases (inferInstance : (Subgroup.center X).Normal).eq_bot_or_eq_top with h0 | h1
  · exact h0
  · exfalso
    obtain ⟨x, y, hxy⟩ := alt7_noncomm
    have hx : e.symm x ∈ Subgroup.center X := h1 ▸ Subgroup.mem_top _
    have h2 := congrArg e (Subgroup.mem_center_iff.1 hx (e.symm y))
    exact hxy (by simpa using h2.symm)

theorem isAltType_seven_quot_center {X : Type} [Group X]
    (h : IsAltType 7 X ∨ IsHatSeven X) : IsAltType 7 (X ⧸ Subgroup.center X) := by
  rcases h with h | h
  · have hc := center_eq_bot_of_isAltType_seven h
    obtain ⟨e⟩ := h
    exact ⟨((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).trans e⟩
  · exact h.2.2

theorem ty7_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : IsAltType 7 X ∨ IsHatSeven X) :
    IsAltType 7 Y ∨ IsHatSeven Y := by
  rcases h with h | h
  · obtain ⟨f⟩ := h
    exact Or.inl ⟨e.symm.trans f⟩
  · exact Or.inr (sec9_isHatSeven_of_mulEquiv e h)

theorem isQuasisimple_of_ty7 {X : Type} [Group X] (h : IsAltType 7 X ∨ IsHatSeven X) :
    CFSG.Open.IsQuasisimple X := by
  rcases h with h | h
  · obtain ⟨e⟩ := h
    have hs : IsSimpleGroup X := e.isSimpleGroup_congr.2 S7.isSimple_Alt7
    have hc := center_eq_bot_of_isAltType_seven ⟨e⟩
    refine ⟨?_, ?_⟩
    · have hA7 : commutator ↥(alternatingGroup (Fin 7)) = ⊤ :=
        commutator_alternatingGroup_eq_top (by simp)
      have h1 := congrArg (Subgroup.map e.symm.toMonoidHom) hA7
      rw [commutator, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective] at h1
      rw [commutator]
      exact h1
    · exact ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).isSimpleGroup_congr.2 hs
  · obtain ⟨hc, hcard, ⟨f⟩⟩ := h
    exact ⟨hc, f.isSimpleGroup_congr.2 S7.isSimple_Alt7⟩

theorem eq_bot_of_normal_of_ty7 {X : Type} [Group X] [Finite X]
    (h : IsAltType 7 X ∨ IsHatSeven X) (N : Subgroup X) [N.Normal] (h3 : ¬ 3 ∣ Nat.card ↥N) :
    N = ⊥ := by
  have h3X := three_dvd_of_ty7 h
  rcases h with h | hh
  · haveI : IsSimpleGroup X := h.some.isSimpleGroup_congr.2 S7.isSimple_Alt7
    rcases (inferInstance : N.Normal).eq_bot_or_eq_top with h0 | h1
    · exact h0
    · exfalso
      apply h3
      rw [h1, Subgroup.card_top]
      exact h3X
  · obtain ⟨hperf, hZcard, ⟨f⟩⟩ := hh
    haveI : IsSimpleGroup (X ⧸ Subgroup.center X) := f.isSimpleGroup_congr.2 S7.isSimple_Alt7
    haveI hNm : (N.map (QuotientGroup.mk' (Subgroup.center X))).Normal :=
      Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
    rcases hNm.eq_bot_or_eq_top with h0 | h1
    · have hNZ : N ≤ Subgroup.center X := fun n hn => by
        have : QuotientGroup.mk' (Subgroup.center X) n ∈
            N.map (QuotientGroup.mk' (Subgroup.center X)) := ⟨n, hn, rfl⟩
        rw [h0, Subgroup.mem_bot] at this
        exact (QuotientGroup.eq_one_iff n).1 this
      have hdvd : Nat.card ↥N ∣ Nat.card ↥(Subgroup.center X) := Subgroup.card_dvd_of_le hNZ
      rw [hZcard] at hdvd
      have h1' : Nat.card ↥N = 1 := by
        rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h1
        · exact h1
        · exfalso
          apply h3
          rw [h1]
      exact Subgroup.eq_bot_of_card_eq _ h1'
    · exfalso
      apply h3
      haveI : Group.IsSolvable ↥(Subgroup.center X) := inferInstance
      have hsplit : ∀ g : X, ∃ m ∈ N, ∃ n ∈ Subgroup.center X, g = m * n := by
        intro g
        have hg : QuotientGroup.mk' (Subgroup.center X) g ∈
            N.map (QuotientGroup.mk' (Subgroup.center X)) := by
          rw [h1]
          exact Subgroup.mem_top _
        obtain ⟨m, hm, hmg⟩ := hg
        have : m⁻¹ * g ∈ Subgroup.center X := (QuotientGroup.eq).1 hmg
        exact ⟨m, hm, m⁻¹ * g, this, by simp⟩
      have htop := eq_top_of_perfect_of_solvable hperf (M₀ := N) (N := Subgroup.center X) inferInstance hsplit
      rw [htop, Subgroup.card_top]
      exact h3X

theorem primeCore_le_pCore_two_of_ty7 {G : Type} [Group G] [Finite G] {J : Subgroup G}
    (h : IsAltType 7 (↥J ⧸ CFSG.pCore 2 ↥J) ∨ IsHatSeven (↥J ⧸ CFSG.pCore 2 ↥J)) :
    GLAPPrimeCore 3 ↥J ≤ CFSG.pCore 2 ↥J := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P : Subgroup ↥J := CFSG.pCore 2 ↥J with hP
  set N : Subgroup ↥J := GLAPPrimeCore 3 ↥J with hN
  haveI : (N.map (QuotientGroup.mk' P)).Normal :=
    (GLAPPrimeCore.normal 3 ↥J).map _ (QuotientGroup.mk'_surjective P)
  have hcop : ¬ 3 ∣ Nat.card ↥(N.map (QuotientGroup.mk' P)) := by
    intro hd
    have h1 : Nat.card ↥(N.map (QuotientGroup.mk' P)) ∣ Nat.card ↥N := Subgroup.card_map_dvd _ _
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 CFSG.pPrimeCore_coprime_card
      (hd.trans h1)
  have hbot := eq_bot_of_normal_of_ty7 h _ hcop
  intro n hn
  have : QuotientGroup.mk' P n ∈ N.map (QuotientGroup.mk' P) := ⟨n, hn, rfl⟩
  rw [hbot, Subgroup.mem_bot] at this
  exact (QuotientGroup.eq_one_iff n).1 this

theorem not_three_dvd_pCore_two {X : Type} [Group X] [Finite X] :
    ¬ 3 ∣ Nat.card ↥(CFSG.pCore 2 X) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := X)).exists_card_eq
  rw [hk]
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
    (Nat.Coprime.pow_right k (by norm_num))

end Types

section SubnormalAux

variable {G : Type} [Group G]

theorem subgroupOf_inf_normal {H M Y : Subgroup G} (hH : (H.subgroupOf M).Normal) :
    ((H ⊓ Y).subgroupOf (M ⊓ Y)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hn' : (n : G) ∈ H ⊓ Y := Subgroup.mem_subgroupOf.1 hn
  have hm : (n : G) ∈ M := (inf_le_left : M ⊓ Y ≤ M) n.2
  have hgM : (g : G) ∈ M := (inf_le_left : M ⊓ Y ≤ M) g.2
  have hgY : (g : G) ∈ Y := (inf_le_right : M ⊓ Y ≤ Y) g.2
  have h1 : (g : G) * n * (g : G)⁻¹ ∈ H := by
    have := hH.conj_mem ⟨n, hm⟩ (Subgroup.mem_subgroupOf.2 hn'.1) ⟨g, hgM⟩
    simpa using Subgroup.mem_subgroupOf.1 this
  have h2 : (g : G) * n * (g : G)⁻¹ ∈ Y :=
    Y.mul_mem (Y.mul_mem hgY hn'.2) (Y.inv_mem hgY)
  refine Subgroup.mem_subgroupOf.2 ?_
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  exact ⟨h1, h2⟩

end SubnormalAux

theorem eq_of_subnormal_perfect {Y : Type} [Group Y] [Finite Y] {K J : Subgroup Y}
    (hq : CFSG.Open.IsQuasisimple ↥K) (hsn : IsSubnormal J K) (hperf : ⁅J, J⁆ = J)
    (hne : J ≠ ⊥) : J = K := by
  by_contra hJK
  obtain ⟨M', hJM', hM'K, hM'ne, hM'n, -⟩ := isSubnormal_exists_normal hsn hJK
  have hcen : M'.subgroupOf K ≤ Subgroup.center ↥K := by
    haveI := hM'n
    refine l119_normal_le_center hq ?_
    intro htop
    exact hM'ne (le_antisymm hM'K (Subgroup.subgroupOf_eq_top.1 htop))
  apply hne
  have hcomm : ∀ x ∈ J, ∀ y ∈ J, x * y = y * x := by
    intro x hx y hy
    have hxc : (⟨x, isSubnormal_le' hsn hx⟩ : ↥K) ∈ Subgroup.center ↥K :=
      hcen ((Subgroup.mem_subgroupOf).2 (hJM' hx))
    have := Subgroup.mem_center_iff.1 hxc ⟨y, isSubnormal_le' hsn hy⟩
    exact (congrArg Subtype.val this).symm
  rw [eq_bot_iff, ← hperf]
  refine Subgroup.commutator_le.2 fun x hx y hy => ?_
  rw [commutatorElement_def, hcomm x hx y hy]
  simp

section Core

structure Cex126 (G : Type) [Group G] [Finite G] (m : ℕ) (B M E A : Subgroup G) (a : G)
    (J : Subgroup G) (z : G) (J₀ : Subgroup G) : Prop where
  sec : Sec11 G m 3 B M E A
  ha : a ∈ A
  ha1 : a ≠ 1
  hnD : ∀ A₁ : Subgroup G, inD 3 M A₁ → a ∉ A₁
  hJ : IsTwoPrimeComp (alphaOf 3 M ⊓ Cg a) J
  hnot : ¬ IsSubnormal J (Cg a)
  hz : z ∈ E ⊓ A
  hz3 : orderOf z = 3
  hJ₀ : GLAPComponent 3 (Cg2 z a) J₀
  hJ₀J : J₀ ≤ J
  hcov : ∀ j ∈ J, ∃ j₀ ∈ J₀, j₀⁻¹ * j ∈ pCoreOf 2 J
  ty2 : IsAltType 7 (↥J ⧸ CFSG.pCore 2 ↥J) ∨ IsHatSeven (↥J ⧸ CFSG.pCore 2 ↥J)
  ty3 : IsAltType 7 (barOf 3 J₀) ∨ IsHatSeven (barOf 3 J₀)

namespace Cex126

variable {G : Type} [Group G] [Finite G] {m : ℕ} {B M E A : Subgroup G} {a : G} {J : Subgroup G}
  {z : G} {J₀ : Subgroup G} (c : Cex126 G m B M E A a J z J₀)

include c

theorem hApow : ∀ x ∈ A, x ^ 3 = 1 := by
  obtain ⟨hDDp, -⟩ := c.sec.pair
  obtain ⟨-, hDp, -⟩ := hDDp
  obtain ⟨hSCs, -⟩ := hDp
  obtain ⟨hSCp, -⟩ := hSCs
  obtain ⟨-, hAel, -⟩ := hSCp
  exact fun x hx => hAel.2 x hx

theorem hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
  obtain ⟨hDDp, -⟩ := c.sec.pair
  obtain ⟨-, hDp, -⟩ := hDDp
  obtain ⟨hSCs, -⟩ := hDp
  obtain ⟨hSCp, -⟩ := hSCs
  obtain ⟨-, hAel, -⟩ := hSCp
  exact fun x hx y hy => congrArg Subtype.val (hAel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem a3 : orderOf a = 3 :=
  orderOf_eq_prime (c.hApow a c.ha) c.ha1

theorem hzA : z ∈ A := c.hz.2

theorem hza : z * a = a * z := c.hAcomm z c.hzA a c.ha

theorem zC : z ∈ Cg a := Subgroup.mem_centralizer_singleton_iff.2 c.hza

theorem J₀perf : ⁅J₀, J₀⁆ = J₀ := glaPComponent_perfect c.hJ₀

theorem three_dvd_J₀ : 3 ∣ Nat.card ↥J₀ := by
  have h1 : 3 ∣ Nat.card (↥J₀ ⧸ GLAPPrimeCore 3 ↥J₀) := three_dvd_of_ty7 c.ty3
  exact h1.trans (Subgroup.card_quotient_dvd_card _)

theorem three_dvd_J : 3 ∣ Nat.card ↥J :=
  c.three_dvd_J₀.trans (Subgroup.card_dvd_of_le c.hJ₀J)

theorem hJM : J ≤ M := c.hJ.1.trans (inf_le_left.trans (alphaOf_le 3 M))

theorem hJ₀M : J₀ ≤ M := c.hJ₀J.trans c.hJM

theorem hJ₀C : J₀ ≤ Cg a := by
  have := c.hJ₀.1
  unfold Cg2 at this
  rw [l119_cg2_eq] at this
  exact this.trans inf_le_left

theorem subnormal_X_Y : IsSubnormal (alphaOf 3 M ⊓ Cg a) (M ⊓ Cg a) := by
  have hn : ((alphaOf 3 M).subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (alphaOf_le 3 M)).2 (le_normalizer_alphaOf 3 M)
  exact IsSubnormal.step (inf_le_inf_right _ (alphaOf_le 3 M)) (subgroupOf_inf_normal hn)
    (IsSubnormal.refl _)

theorem hJ3 : GLAPComponent 3 (M ⊓ Cg a) J :=
  glaPComponent_of_twoPrimeComp c.hJ c.subnormal_X_Y c.three_dvd_J

theorem key (S : Set (Subgroup G)) (hS : ∀ L ∈ S, GLAPComponent 3 (Cg a) L)
    (hSM : ∀ L ∈ S, L ≤ M) (hJ₀S : J₀ ≤ ⨆ L ∈ S, L) : False := by
  have hS' : ∀ L ∈ S, GLAPComponent 3 (M ⊓ Cg a) L := fun L hL =>
    glaPComponent_of_le Nat.prime_three (hS L hL) (le_inf (hSM L hL) (hS L hL).1) inf_le_right
  obtain ⟨L, hLS, hJL⟩ := exists_glaPComponent_eq_of_family c.hJ3 hS' c.hJ₀J hJ₀S c.J₀perf
    c.three_dvd_J₀
  apply c.hnot
  rw [hJL]
  exact (hS L hLS).2.1

theorem le_M_of_central_action (h111 : Prop111Statement) {L : Subgroup G}
    (hL : GLAPComponent 3 (Cg a) L) (hzL : z ∈ Subgroup.normalizer (L : Set G))
    (hJ₀L : GLAPComponent 3 (L ⊓ Cg z) J₀)
    (hcent : ∀ q ∈ barX 3 (Cg a) L, bar3 a z c.zC * q = q * bar3 a z c.zC) : L ≤ M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLC : L ≤ Cg a := hL.1
  have hd : IsPGroup 3 (Subgroup.zpowers z) := l119_isPGroup_zpowers (by
    rw [← c.hz3]
    exact pow_orderOf_eq_one z)
  have hKbc : IsComponentOf (barX 3 (Cg a) L) ⊤ := hL.2.2.1
  have hJb := glaPComponent_barX_inf_centralizer (p := 3) Nat.prime_three (M := Cg a) c.zC hLC hzL hd hJ₀L
  have hcenL : barX 3 (Cg a) L ≤ Subgroup.centralizer
      ({bar3 a z c.zC} : Set (↥(Cg a) ⧸ GLAPPrimeCore 3 ↥(Cg a))) := by
    intro q hq
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hcent q hq).symm
  rw [inf_eq_left.2 hcenL] at hJb
  have hJbperf : ⁅barX 3 (Cg a) J₀, barX 3 (Cg a) J₀⁆ = barX 3 (Cg a) J₀ :=
    barX_perfect 3 c.hJ₀C c.J₀perf
  have hJbne : barX 3 (Cg a) J₀ ≠ ⊥ := barX_ne_bot_of_three_dvd c.hJ₀C c.three_dvd_J₀
  have hJbK : barX 3 (Cg a) J₀ = barX 3 (Cg a) L :=
    eq_of_subnormal_perfect hKbc.2.2 hJb.2.1 hJbperf hJbne
  have h11 := h111 c.sec c.ha c.ha1
  intro l hl
  obtain ⟨j, hj, hjl⟩ := exists_of_barX_le (le_of_eq hJbK.symm) hl (hLC hl)
  have := M.mul_mem (c.hJ₀M hj) (h11 hjl)
  simpa using this

end Cex126

end Core

section Single

variable {G : Type} [Group G] [Finite G]

theorem zmod3_one_ne_zero : (1 : ZMod 3) ≠ 0 := by decide

theorem three_dvd_card_barX {Y J : Subgroup G} (hJY : J ≤ Y) (h3 : 3 ∣ Nat.card ↥J) :
    3 ∣ Nat.card ↥(barX 3 Y J) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥J) 3 h3
  have hg3 : (g : G) ^ 3 = 1 := by
    have := pow_orderOf_eq_one g
    rw [hg] at this
    exact congrArg Subtype.val this
  let x : ↥(barX 3 Y J) := ⟨QuotientGroup.mk' (GLAPPrimeCore 3 ↥Y) ⟨(g : G), hJY g.2⟩,
    ⟨⟨(g : G), hJY g.2⟩, (Subgroup.mem_subgroupOf).2 g.2, rfl⟩⟩
  have hx : orderOf x = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · apply Subtype.ext
      show (QuotientGroup.mk' (GLAPPrimeCore 3 ↥Y) ⟨(g : G), hJY g.2⟩) ^ 3 = 1
      rw [← map_pow]
      have : (⟨(g : G), hJY g.2⟩ : ↥Y) ^ 3 = 1 := Subtype.ext (by simpa using hg3)
      rw [this, map_one]
    · intro h1
      have h2 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥Y) ⟨(g : G), hJY g.2⟩ = 1 := congrArg Subtype.val h1
      have h3' := l119_eq_one_of_pow_of_mem_core Nat.prime_three
        (x := ⟨(g : G), hJY g.2⟩) (Subtype.ext (by simpa using hg3)) ((QuotientGroup.eq_one_iff _).1 h2)
      have : (g : G) = 1 := congrArg Subtype.val h3'
      have : g = 1 := Subtype.ext this
      rw [this, orderOf_one] at hg
      omega
  have := orderOf_dvd_natCard x
  rwa [hx] at this

theorem primeCoreOf_barX_le {Y U : Subgroup G} (hUY : U ≤ Y) :
    GLAPPrimeCoreOf 3 (barX 3 Y U) ≤ barX 3 Y (GLAPPrimeCoreOf 3 U) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ψ : ↥Y →* ↥Y ⧸ GLAPPrimeCore 3 ↥Y := QuotientGroup.mk' (GLAPPrimeCore 3 ↥Y) with hψ
  set A : Subgroup ↥Y := U.subgroupOf Y with hA
  have hker : Nat.Coprime 3 (Nat.card ↥(A ⊓ ψ.ker)) := by
    rw [hψ, QuotientGroup.ker_mk']
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
      CFSG.pPrimeCore_coprime_card
  have hmap := glaPPrimeCore_map_subgroupMap Nat.prime_three ψ A hker
  have hiso := glaPPrimeCore_map_iso 3 (Subgroup.subgroupOfEquivOfLe hUY)
  rintro y ⟨x, hx, rfl⟩
  have hx' : x ∈ (GLAPPrimeCore 3 ↥A).map (ψ.subgroupMap A) := by
    rw [hmap]
    exact hx
  obtain ⟨u, hu, hux⟩ := hx'
  have hu' : (Subgroup.subgroupOfEquivOfLe hUY) u ∈ GLAPPrimeCore 3 ↥U := by
    rw [← hiso]
    exact Subgroup.mem_map_of_mem _ hu
  refine ⟨(u : ↥Y), ?_, ?_⟩
  · refine (Subgroup.mem_subgroupOf).2 ?_
    exact ⟨_, hu', rfl⟩
  · rw [← hux]
    rfl

theorem bar3_mem_normalizer_aux {G : Type} [Group G] [Finite G] {a : G} {L : Subgroup G} (hLC : L ≤ Cg a)
    {e : G} (heC : e ∈ Cg a) (heL : e ∈ Subgroup.normalizer (L : Set G)) :
    bar3 a e heC ∈ Subgroup.normalizer ((barX 3 (Cg a) L : Subgroup _) : Set _) := by
  have h1 := l119_barX_gLBConj (p := 3) (C := Cg a) (H := L) heC hLC
  rw [mem_normalizer_iff_gLBConj_eq.1 heL] at h1
  exact mem_normalizer_iff_gLBConj_eq.2 h1.symm

@[expose] def Good126 (E A : Subgroup G) (a : G) (L : Subgroup G) : Prop :=
  ∀ e ∈ E ⊓ A, e ≠ 1 → ∃ heC : e ∈ Cg a, e ∈ Subgroup.normalizer (L : Set G) ∧
    ∃ q ∈ barX 3 (Cg a) L, bar3 a e heC * q ≠ q * bar3 a e heC

namespace Cex126

variable {m : ℕ} {B M E A : Subgroup G} {a : G} {J : Subgroup G} {z : G} {J₀ : Subgroup G}
  (c : Cex126 G m B M E A a J z J₀)

include c

theorem hA0el : IsElemAbelian 3 (E ⊓ A) := by
  obtain ⟨hDDp, -⟩ := c.sec.pair
  obtain ⟨-, hDp, -⟩ := hDDp
  obtain ⟨hSCs, -⟩ := hDp
  obtain ⟨hSCp, -⟩ := hSCs
  obtain ⟨-, hAel, -⟩ := hSCp
  exact l119_isElemAbelian_of_le inf_le_right hAel

theorem hA0rank : 2 ≤ CFSG.Open.pRank 3 (E ⊓ A) := by
  obtain ⟨hDDp, -⟩ := c.sec.pair
  exact hDDp.2.2

theorem hACg : A ≤ Cg a := fun x hx => by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact c.hAcomm a c.ha x hx |>.symm

theorem hA0C : E ⊓ A ≤ Cg a := inf_le_right.trans c.hACg

theorem hA0p : IsPGroup 3 ↥(E ⊓ A) := isPGroup_of_isElemAbelian' c.hA0el

theorem bar_elemAbelian : IsElemAbelian 3 (barX 3 (Cg a) (E ⊓ A)) :=
  isElemAbelian_barX c.hA0el

theorem bar_rank : 2 ≤ CFSG.Open.pRank 3 (barX 3 (Cg a) (E ⊓ A)) := by
  rw [rank_barX_of_isPGroup Nat.prime_three c.hA0p c.hA0C]
  exact c.hA0rank

theorem exists_of_mem_bar {b : ↥(Cg a) ⧸ GLAPPrimeCore 3 ↥(Cg a)}
    (hb : b ∈ barX 3 (Cg a) (E ⊓ A)) :
    ∃ (e : G) (he : e ∈ E ⊓ A) (heC : e ∈ Cg a), bar3 a e heC = b := by
  obtain ⟨x, hx, rfl⟩ := hb
  exact ⟨(x : G), (Subgroup.mem_subgroupOf).1 hx, x.2, rfl⟩

theorem bar_pow {e : G} (he : e ∈ E ⊓ A) (heC : e ∈ Cg a) : bar3 a e heC ^ 3 = 1 := by
  rw [← map_pow]
  have : (⟨e, heC⟩ : ↥(Cg a)) ^ 3 = 1 := Subtype.ext (by simpa using c.hApow e he.2)
  rw [this, map_one]

theorem le_M_of_barX_le (h111 : Prop111Statement) {L : Subgroup G} (hLC : L ≤ Cg a)
    (h : barX 3 (Cg a) L ≤ barX 3 (Cg a) M) : L ≤ M := by
  intro l hl
  obtain ⟨m', hm, hml⟩ := exists_of_barX_le h hl (hLC hl)
  have := M.mul_mem hm (h111 c.sec c.ha c.ha1 hml)
  simpa using this

theorem layer_le_M_bar (h115 : Prop115Statement) (Ty : ∀ (X : Type) [Group X], Prop)
    (hTyiso : ∀ (X Y : Type) [Group X] [Group Y], (X ≃* Y) → Ty X → Ty Y)
    (hnb : ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsQuasisimple X →
      Ty (X ⧸ Subgroup.center X) → ¬ IsLocallyOTwoBalancedWrtP 3 1 X ∧ ¬ IsLTwoTwentySeven X)
    {L : Subgroup G} (hL : GLAPComponent 3 (Cg a) L) {e : G} (he : e ∈ E ⊓ A) (he1 : e ≠ 1)
    (heC : e ∈ Cg a)
    (hQty : ∀ Q : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore 3 ↥(Cg a)),
      GLAPComponent 3 (barX 3 (Cg a) L ⊓ Subgroup.centralizer
        ({bar3 a e heC} : Set (↥(Cg a) ⧸ GLAPPrimeCore 3 ↥(Cg a)))) Q → Ty (barZ3 Q)) :
    GLAPLayer 3 (barX 3 (Cg a) L ⊓ Subgroup.centralizer
        ({bar3 a e heC} : Set (↥(Cg a) ⧸ GLAPPrimeCore 3 ↥(Cg a)))) ≤ barX 3 (Cg a) M := by
  unfold GLAPLayer
  refine sSup_le fun Q hQ => ?_
  have hnD' : ¬ ∃ A1 : Subgroup G, inD 3 M A1 ∧ a ∈ A1 := fun ⟨A1, hA1, haA1⟩ => c.hnD A1 hA1 haA1
  exact layer_le_gen Nat.prime_three Ty hTyiso hnb c.sec c.ha c.ha1 hnD' h115 he he1 heC
    (l119_isPGroup_zpowers (c.hApow e he.2)) hL.2.2.1.2.1 hQ (hQty Q hQ)

theorem primeCore_le_M_bar (h112 : Prop112Statement) {L : Subgroup G}
    (hL : GLAPComponent 3 (Cg a) L) {e : G} (he : e ∈ E ⊓ A) (he1 : e ≠ 1) (heC : e ∈ Cg a)
    (heL : e ∈ Subgroup.normalizer (L : Set G)) :
    GLAPPrimeCoreOf 3 (barX 3 (Cg a) L ⊓ Subgroup.centralizer
        ({bar3 a e heC} : Set (↥(Cg a) ⧸ GLAPPrimeCore 3 ↥(Cg a)))) ≤ barX 3 (Cg a) M := by
  have hLC : L ≤ Cg a := hL.1
  have hdp : IsPGroup 3 (Subgroup.zpowers e) := l119_isPGroup_zpowers (c.hApow e he.2)
  have hbar := barX_inf_centralizer Nat.prime_three heC hLC heL hdp
  rw [← hbar]
  refine (primeCoreOf_barX_le (inf_le_left.trans hLC)).trans (barX_mono ?_)
  have hsub : IsSubnormal (L ⊓ Cg e) (Cg2 e a) := by
    have h := isSubnormal_inf hL.2.1 (Cg e)
    unfold Cg2
    rw [l119_cg2_eq]
    exact h
  refine (glaPPrimeCoreOf_le_of_isSubnormal Nat.prime_three hsub).trans ?_
  rcases h112 c.sec c.ha c.ha1 he he1 with h | ⟨A1, hA1, haA1⟩
  · exact h
  · exact absurd haA1 (c.hnD A1 hA1)

theorem hBnorm_of_good {L : Subgroup G} (hLC : L ≤ Cg a) (hgood : Good126 E A a L) :
    barX 3 (Cg a) (E ⊓ A) ≤ Subgroup.normalizer ((barX 3 (Cg a) L : Subgroup _) : Set _) := by
  intro b hb
  obtain ⟨e, he, heC, rfl⟩ := c.exists_of_mem_bar hb
  by_cases he1 : e = 1
  · subst he1
    have : bar3 a 1 heC = 1 := by
      show QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cg a)) ⟨1, heC⟩ = 1
      exact map_one _
    rw [this]
    exact Subgroup.one_mem _
  · obtain ⟨heC', hnorm, -⟩ := hgood e he he1
    exact bar3_mem_normalizer_aux hLC heC hnorm

theorem hfaith_of_good {L : Subgroup G} (hgood : Good126 E A a L) :
    ∀ b ∈ barX 3 (Cg a) (E ⊓ A), b ≠ 1 → ∃ q ∈ barX 3 (Cg a) L, b * q ≠ q * b := by
  intro b hb hb1
  obtain ⟨e, he, heC, rfl⟩ := c.exists_of_mem_bar hb
  have he1 : e ≠ 1 := by
    rintro rfl
    apply hb1
    show QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cg a)) ⟨1, heC⟩ = 1
    exact map_one _
  obtain ⟨heC', -, q, hq, hqne⟩ := hgood e he he1
  exact ⟨q, hq, hqne⟩

end Cex126

theorem bar3_mem_normalizer {a : G} {L : Subgroup G} (hLC : L ≤ Cg a) {e : G} (heC : e ∈ Cg a)
    (heL : e ∈ Subgroup.normalizer (L : Set G)) :
    bar3 a e heC ∈ Subgroup.normalizer ((barX 3 (Cg a) L : Subgroup _) : Set _) := by
  have h1 := l119_barX_gLBConj (p := 3) (C := Cg a) (H := L) heC hLC
  rw [mem_normalizer_iff_gLBConj_eq.1 heL] at h1
  exact mem_normalizer_iff_gLBConj_eq.2 h1.symm

theorem isLpType_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {p Q : ℕ}
    (h : IsLpType p Q X) : IsLpType p Q Y := by
  obtain ⟨F, hF, hfin, hcard, ⟨f⟩⟩ := h
  exact ⟨F, hF, hfin, hcard, ⟨e.symm.trans f⟩⟩

namespace Cex126

variable {m : ℕ} {B M E A : Subgroup G} {a : G} {J : Subgroup G} {z : G} {J₀ : Subgroup G}
  (c : Cex126 G m B M E A a J z J₀)

include c

theorem central_product (sib : Sib126) {W I : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore 3 ↥(Cg a))}
    (hW : W ≤ barX 3 (Cg a) M) (hI : I = ⨆ w ∈ W, GLBConj w (barX 3 (Cg a) J₀)) :
    ∃ (ι : Type) (Q : ι → Subgroup (↥I ⧸ CFSG.pCore 2 ↥I)),
      (∀ i, IsAltType 7 ↥(Q i) ∨ IsHatSeven ↥(Q i)) ∧
      (∀ i j, i ≠ j → ∀ x ∈ Q i, ∀ y ∈ Q j, x * y = y * x) ∧ (⨆ i, Q i) = ⊤ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJC : J ≤ Cg a := c.hJ.1.trans inf_le_right
  have hT : Tof 3 M a ≤ pCoreOf 2 (Cg a) := by
    by_contra hn
    exact sib.h121 ⟨c.sec, ⟨c.ha, c.ha1⟩, hn⟩
  have hO2J : pCoreOf 2 J ≤ GLAPPrimeCoreOf 3 (Cg a) :=
    ((pCoreOf_le_of_isSubnormal 2 c.hJ.2.1).trans hT).trans
      (Subgroup.map_mono (pCore_two_le_primeCore_three ↥(Cg a)))
  have hbarJ : barX 3 (Cg a) J = barX 3 (Cg a) J₀ := by
    refine le_antisymm ?_ (barX_mono c.hJ₀J)
    refine barX_le_of_forall c.hJ₀C (fun k hk => ?_)
    obtain ⟨j₀, hj₀, ho⟩ := c.hcov k hk
    exact ⟨j₀, hj₀, hO2J ho⟩
  have hker : (barMap 3 hJC).ker = CFSG.pCore 2 ↥J := by
    ext l
    rw [MonoidHom.mem_ker]
    constructor
    · intro h1
      have h2 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cg a)) (Subgroup.inclusion hJC l) = 1 :=
        congrArg Subtype.val h1
      have h3 : Subgroup.inclusion hJC l ∈ GLAPPrimeCore 3 ↥(Cg a) :=
        (QuotientGroup.eq_one_iff _).1 h2
      have hl3 : l ∈ GLAPPrimeCore 3 ↥J := by
        set N' : Subgroup ↥J := (GLAPPrimeCoreOf 3 (Cg a)).subgroupOf J with hN'
        have hnorm : N'.Normal := ⟨fun n hn g => by
          have := (Subgroup.mem_normalizer_iff.1
            (le_normalizer_glaPPrimeCoreOf 3 (Cg a) (hJC g.2)) (n : G)).1
            ((Subgroup.mem_subgroupOf).1 hn)
          exact (Subgroup.mem_subgroupOf).2 (by simpa using this)⟩
        have hcop : Nat.Coprime 3 (Nat.card N') := by
          refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 fun hd => ?_
          refine not_dvd_card_glaPPrimeCoreOf Nat.prime_three (Cg a) (hd.trans ?_)
          have hc : Nat.card (N'.map J.subtype) = Nat.card N' :=
            Subgroup.card_map_of_injective J.subtype_injective
          rw [← hc]
          refine Subgroup.card_dvd_of_le ?_
          rintro _ ⟨k, hk, rfl⟩
          exact (Subgroup.mem_subgroupOf).1 hk
        have hle : N' ≤ GLAPPrimeCore 3 ↥J := le_sSup ⟨hnorm, hcop⟩
        exact hle ((Subgroup.mem_subgroupOf).2 ⟨_, h3, rfl⟩)
      exact primeCore_le_pCore_two_of_ty7 c.ty2 hl3
    · intro hl
      apply Subtype.ext
      show QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cg a)) (Subgroup.inclusion hJC l) = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      have hl' : ((l : ↥J) : G) ∈ pCoreOf 2 J := ⟨l, hl, rfl⟩
      obtain ⟨x, hx, hxl⟩ := hO2J hl'
      have : Subgroup.inclusion hJC l = x := Subtype.ext hxl.symm
      rw [this]
      exact hx
  have hJbarTy : IsAltType 7 ↥(barX 3 (Cg a) J) ∨ IsHatSeven ↥(barX 3 (Cg a) J) := by
    let e : (↥J ⧸ CFSG.pCore 2 ↥J) ≃* ↥(barX 3 (Cg a) J) :=
      (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective (barMap 3 hJC) (barMap_surjective hJC))
    exact ty7_congr e c.ty2
  have hPty : ∀ w : ↥(Cg a) ⧸ GLAPPrimeCore 3 ↥(Cg a),
      IsAltType 7 ↥(GLBConj w (barX 3 (Cg a) J₀)) ∨ IsHatSeven ↥(GLBConj w (barX 3 (Cg a) J₀)) := by
    intro w
    rw [← hbarJ]
    exact ty7_congr (l119_gLBConj_equiv w _) hJbarTy
  set X : Subgroup G := alphaOf 3 M ⊓ Cg a with hX
  have hXconj : ∀ y ∈ M, y ∈ Cg a → GLBConj y X = X := by
    intro y hyM hyC
    rw [hX, gLBConj_inf, mem_normalizer_iff_gLBConj_eq.1 (le_normalizer_alphaOf 3 M hyM),
      mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer hyC)]
  have hconj : ∀ w ∈ W, IsSubnormal (GLBConj w (barX 3 (Cg a) J₀)) (barX 3 (Cg a) X) := by
    intro w hw
    obtain ⟨y', hy', rfl⟩ := hW hw
    have hyM : (y' : G) ∈ M := (Subgroup.mem_subgroupOf).1 hy'
    have h1 := l119_barX_gLBConj (p := 3) (C := Cg a) (H := J) y'.2 hJC
    rw [hbarJ] at h1
    rw [← h1]
    have h2 := isSubnormal_gLBConj c.hJ.2.1 (y' : G)
    rw [hXconj _ hyM y'.2] at h2
    exact isSubnormal_barX 3 h2
  have hIX : I ≤ barX 3 (Cg a) X := by
    rw [hI]
    exact iSup₂_le fun w hw => isSubnormal_le' (hconj w hw)
  have hPI : ∀ w ∈ W, GLBConj w (barX 3 (Cg a) J₀) ≤ I := fun w hw => by
    rw [hI]
    exact le_iSup₂_of_le w hw le_rfl
  have hPsnI : ∀ w ∈ W, IsSubnormal (GLBConj w (barX 3 (Cg a) J₀)) I := fun w hw =>
    isSubnormal_of_le_of_le (hconj w hw) (hPI w hw) hIX
  let π' : ↥I →* ↥I ⧸ CFSG.pCore 2 ↥I := QuotientGroup.mk' (CFSG.pCore 2 ↥I)
  let img : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore 3 ↥(Cg a)) → Subgroup (↥I ⧸ CFSG.pCore 2 ↥I) :=
    fun P => (P.subgroupOf I).map π'
  have hQe : ∀ w ∈ W, ∃ e : ↥(GLBConj w (barX 3 (Cg a) J₀)) ≃*
      ↥(img (GLBConj w (barX 3 (Cg a) J₀))), True := by
    intro w hw
    have hP2 : CFSG.pCore 2 ↥(GLBConj w (barX 3 (Cg a) J₀)) = ⊥ :=
      eq_bot_of_normal_of_ty7 (hPty w) _ not_three_dvd_pCore_two
    have e1 := quotEquivTwoImage (hPI w hw) (hPsnI w hw)
    exact ⟨((QuotientGroup.quotientMulEquivOfEq hP2).trans QuotientGroup.quotientBot).symm.trans e1,
      trivial⟩
  refine ⟨{Q : Subgroup (↥I ⧸ CFSG.pCore 2 ↥I) //
    ∃ w ∈ W, Q = img (GLBConj w (barX 3 (Cg a) J₀))}, fun Q => Q.1, ?_, ?_, ?_⟩
  · rintro ⟨Q, w, hw, rfl⟩
    obtain ⟨e, -⟩ := hQe w hw
    exact ty7_congr e (hPty w)
  · rintro ⟨Q, w, hw, rfl⟩ ⟨Q', w', hw', rfl⟩ hne x hx y hy
    have hQc : ∀ w ∈ W, IsComponentOf (img (GLBConj w (barX 3 (Cg a) J₀))) ⊤ := by
      intro w hw
      refine ⟨le_top, ?_, ?_⟩
      · have h1 := isSubnormal_map' π' (isSubnormal_comap' I.subtype (hPsnI w hw))
        rwa [show I.comap I.subtype = ⊤ from Subgroup.subgroupOf_self I,
          Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h1
      · obtain ⟨e, -⟩ := hQe w hw
        exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e
          (isQuasisimple_of_ty7 (hPty w))
    exact comp_comm (hQc w hw) (hQc w' hw') (fun h => hne (Subtype.ext h)) hx hy
  · rw [eq_top_iff]
    intro t _
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective t
    have hsub : (⨆ w ∈ W, GLBConj w (barX 3 (Cg a) J₀)).subgroupOf I ≤
        ⨆ w ∈ W, (GLBConj w (barX 3 (Cg a) J₀)).subgroupOf I := by
      refine (subgroupOf_iSup_le (fun w => ⨆ _ : w ∈ W, GLBConj w (barX 3 (Cg a) J₀))
        fun w => iSup_le fun hw => hPI w hw).trans ?_
      refine iSup_mono fun w => ?_
      exact subgroupOf_iSup_le (fun _ : w ∈ W => GLBConj w (barX 3 (Cg a) J₀))
        fun hw => hPI w hw
    have hu : u ∈ ⨆ w ∈ W, (GLBConj w (barX 3 (Cg a) J₀)).subgroupOf I := by
      refine hsub ?_
      rw [← hI, Subgroup.mem_subgroupOf]
      exact u.2
    have himg : (⨆ w ∈ W, (GLBConj w (barX 3 (Cg a) J₀)).subgroupOf I).map π' ≤
        ⨆ i : {Q : Subgroup (↥I ⧸ CFSG.pCore 2 ↥I) //
          ∃ w ∈ W, Q = img (GLBConj w (barX 3 (Cg a) J₀))}, i.1 := by
      rw [Subgroup.map_iSup]
      refine iSup_le fun w => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hw => ?_
      exact le_iSup_of_le ⟨img (GLBConj w (barX 3 (Cg a) J₀)), w, hw, rfl⟩ le_rfl
    exact himg ⟨u, hu, rfl⟩

theorem hEM : E ≤ M := by
  obtain ⟨hDDp, -⟩ := c.sec.pair
  exact hDDp.1.1.1.1

theorem hzM : z ∈ M := c.hEM c.hz.1

theorem hz3' : z ^ 3 = 1 := by
  rw [← c.hz3]
  exact pow_orderOf_eq_one z

theorem hkp : CFSG.Open.IsKProper G := c.sec.standing.kProper

theorem hCtop : Cg a ≠ ⊤ := centralizer_singleton_ne_top c.sec.standing c.ha1

theorem hz1 : z ≠ 1 := by
  intro h1
  have := c.hz3
  rw [h1, orderOf_one] at this
  omega

end Cex126

end Single

section Assembly

variable {G : Type} [Group G] [Finite G]

theorem three_dvd_alpha {M : Subgroup G} {a : G} {J : Subgroup G}
    (hJ : IsTwoPrimeComp (alphaOf 3 M ⊓ Cg a) J) : 3 ∣ Nat.card ↥(alphaOf 3 M) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra h3
  have hno : ∀ J' : Subgroup G, ¬ (3 = 3 ∧ J' ≤ M ∧ IsSubnormal J' M ∧ ⁅J', J'⁆ = J' ∧
      IsHatSeven (↥J' ⧸ CFSG.pCore 2 ↥J')) := by
    rintro J' ⟨h33, hJ'M, hsn, hperf, hhat⟩
    apply h3
    have hle : J' ≤ alphaOf 3 M := by
      unfold alphaOf
      exact le_sup_of_le_right (le_iSup₂_of_le J' ⟨h33, hJ'M, hsn, hperf, hhat⟩ le_rfl)
    have h1 : 3 ∣ Nat.card (↥J' ⧸ CFSG.pCore 2 ↥J') := three_dvd_of_isHatSeven hhat
    exact (h1.trans (Subgroup.card_quotient_dvd_card _)).trans (Subgroup.card_dvd_of_le hle)
  have hα : alphaOf 3 M = pCoreOf 2 M := by
    unfold alphaOf
    have : (⨆ (J' : Subgroup G) (_ : 3 = 3 ∧ J' ≤ M ∧ IsSubnormal J' M ∧ ⁅J', J'⁆ = J' ∧
        IsHatSeven (↥J' ⧸ CFSG.pCore 2 ↥J')), J') = ⊥ := by
      refine iSup_eq_bot.2 fun J' => iSup_eq_bot.2 fun hJ' => (hno J' hJ').elim
    rw [this, sup_bot_eq]
  have hJα : J ≤ pCoreOf 2 M := by
    rw [← hα]
    exact hJ.1.trans inf_le_left
  have hJ2 : IsPGroup 2 ↥J := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le hJα
  have hperf : commutator ↥J = ⊤ := Group.isPerfect_def.1 (Subgroup.isPerfect_iff.2 hJ.2.2.1)
  haveI := hJ2.isNilpotent
  have hsub : Subsingleton ↥J := by
    by_contra hns
    haveI : Nontrivial ↥J := not_subsingleton_iff_nontrivial.1 hns
    have := IsSolvable.commutator_lt_top_of_nontrivial ↥J
    rw [hperf] at this
    exact lt_irrefl _ this
  have hJbot : J = ⊥ := Subgroup.eq_bot_of_subsingleton J
  have hq := hJ.2.2.2.2.2
  have himg : ((J.subgroupOf (alphaOf 3 M ⊓ Cg a)).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥(alphaOf 3 M ⊓ Cg a)))) = ⊥ := by
    rw [hJbot]
    simp
  rw [himg] at hq
  obtain ⟨x, y, hxy⟩ := hq.2.toNontrivial.exists_pair_ne
  apply hxy
  obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
  rw [Subsingleton.elim x' y']

theorem exists_z_R {m : ℕ} {B M E A : Subgroup G} (h : Sec11 G m 3 B M E A)
    (h3 : 3 ∣ Nat.card ↥(alphaOf 3 M)) :
    ∃ (R : Subgroup G) (z : G), IsSylowIn 3 M R ∧ E ⊔ A ≤ R ∧ z ∈ centerOf R ∧ z ∈ E ⊓ A ∧
      z ∈ alphaOf 3 M ∧ orderOf z = 3 := by
  obtain ⟨R, hR, hER⟩ := Sec12c.prop126_exists_sylow h
  have hαM : alphaOf 3 M ≤ M := alphaOf_le 3 M
  have hnorm : ∀ g ∈ M, ∀ x ∈ alphaOf 3 M, g * x * g⁻¹ ∈ alphaOf 3 M := by
    intro g hg x hx
    have hgN : g ∈ Subgroup.normalizer (alphaOf 3 M : Set G) := le_normalizer_alphaOf 3 M hg
    exact (Subgroup.mem_normalizer_iff.1 hgN x).1 hx
  have h3M : 3 ∣ Nat.card ↥M := h3.trans (Subgroup.card_dvd_of_le hαM)
  have hR1 : R ≠ ⊥ := Prop126.sylow_ne_bot_of_three_dvd hR h3M
  have hne : alphaOf 3 M ⊓ R ≠ ⊥ := Prop126.inf_sylow_ne_bot hR hR1 hαM hnorm h3
  obtain ⟨z, hzα, hzZ, hz3⟩ := Prop126.exists_order_three_central_mem hR.2.1
    (fun r hr x hx => hnorm r (hR.1 hr) x hx) hne
  exact ⟨R, z, hR, hER, hzZ, Sec12c.prop126_central_mem h hER hzZ hz3, hzα, hz3⟩

end Assembly

end Prop126b

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

end
