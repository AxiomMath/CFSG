module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GSplit
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GLayer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GKnown
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRLift
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIAut
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIInnDiag
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MITransport
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156Layer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156Trans
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Cover
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Trans
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T156

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.S3 CFSG.LocalAnalysis.GLTheoremA.MI
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open scoped commutatorElement

section Basic

variable {G : Type} [Group G]

theorem innDiagOn_mono {p : ℕ} {A B L : Subgroup G} (hBA : B ≤ A) (h : InnDiagOn p A L) :
    InnDiagOn p B L :=
  ⟨hBA.trans h.1, Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ hh a ha => hh a (hBA ha)) h.2⟩

theorem indAut_mul {p : ℕ} {L : Subgroup G} {g h : G} (hg : g ∈ Subgroup.normalizer (L : Set G))
    (hh : h ∈ Subgroup.normalizer (L : Set G)) :
    indAut p L (g * h) (Subgroup.mul_mem _ hg hh) = indAut p L h hh * indAut p L g hg := by
  unfold indAut
  rw [← map_mul]
  congr 1
  apply Subtype.ext
  simp

theorem indAut_zpow {p : ℕ} {L : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G)) (k : ℤ) :
    indAut p L (g ^ k) (Subgroup.zpow_mem _ hg k) = indAut p L g hg ^ k := by
  unfold indAut
  rw [← map_zpow]
  congr 1
  apply Subtype.ext
  simp [zpow_neg, inv_zpow]

theorem indAut_pow_eq_one {p : ℕ} {L : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G))
    (hgp : g ^ p = 1) : indAut p L g hg ^ p = 1 := by
  unfold indAut
  rw [← map_pow]
  have h1 : (⟨g⁻¹, Subgroup.inv_mem _ hg⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ p = 1 :=
    Subtype.ext (by simp [inv_pow, hgp])
  rw [h1, map_one]

theorem indAut_one {p : ℕ} {L : Subgroup G} : indAut p L 1 (Subgroup.one_mem _) = 1 := by
  unfold indAut
  have h1 : (⟨(1 : G)⁻¹, Subgroup.inv_mem _ (Subgroup.one_mem _)⟩ :
      ↥(Subgroup.normalizer (L : Set G))) = 1 := Subtype.ext (by simp)
  rw [h1, map_one]

theorem indAut_congr {p : ℕ} {L : Subgroup G} {g g' : G} (h : g = g')
    (hg : g ∈ Subgroup.normalizer (L : Set G)) (hg' : g' ∈ Subgroup.normalizer (L : Set G)) :
    indAut p L g hg = indAut p L g' hg' := by
  subst h
  rfl

end Basic

section Restriction

variable {R : Type} [Group R] (x : MulAut R)

@[expose] noncomputable def resHom :
    ↥(Subgroup.centralizer ({x} : Set (MulAut R))) →* MulAut ↥(ggFixDer x) where
  toFun φ :=
    have hφ : (φ : MulAut R) * x = x * φ :=
      Subgroup.mem_centralizer_singleton_iff.1 φ.2
    have hφ' : (φ : MulAut R)⁻¹ * x = x * (φ : MulAut R)⁻¹ := by
      calc (φ : MulAut R)⁻¹ * x = (φ : MulAut R)⁻¹ * (x * φ) * (φ : MulAut R)⁻¹ := by group
        _ = (φ : MulAut R)⁻¹ * ((φ : MulAut R) * x) * (φ : MulAut R)⁻¹ := by rw [hφ]
        _ = x * (φ : MulAut R)⁻¹ := by group
    { toFun := fun g => ⟨(φ : MulAut R) g, ggFixDer_map_mem hφ g.2⟩
      invFun := fun g => ⟨(φ : MulAut R)⁻¹ g, ggFixDer_map_mem hφ' g.2⟩
      left_inv := fun g => Subtype.ext (by simp)
      right_inv := fun g => Subtype.ext (by simp)
      map_mul' := fun g h => Subtype.ext (by simp) }
  map_one' := by
    ext g
    rfl
  map_mul' := by
    intro φ ψ
    ext g
    rfl

theorem resHom_apply (φ : ↥(Subgroup.centralizer ({x} : Set (MulAut R)))) (g : ↥(ggFixDer x)) :
    ((resHom x φ g : ↥(ggFixDer x)) : R) = (φ : MulAut R) g := rfl

end Restriction

section Core


variable {Ω : Type} [Group Ω] [Finite Ω]

theorem card_le_range_mul {A₀ C : Subgroup Ω} {M : Type*} [Group M] (f : ↥A₀ →* M)
    (hker : ∀ a : ↥A₀, f a = 1 → (a : Ω) ∈ C) : Nat.card A₀ ≤ Nat.card f.range * Nat.card C := by
  rw [← Subgroup.card_ker_mul_card_range f, mul_comm]
  apply Nat.mul_le_mul_left
  refine Nat.card_le_card_of_injective
    (fun a : f.ker => (⟨((a : ↥A₀) : Ω), hker a (MonoidHom.mem_ker.1 a.2)⟩ : C)) ?_
  intro a a' h
  have h1 : ((a : ↥A₀) : Ω) = ((a' : ↥A₀) : Ω) := by
    have := congrArg (fun z : ↥C => (z : Ω)) h
    simpa using this
  exact Subtype.ext (Subtype.ext h1)

theorem isElemAbelian_range {p : ℕ} {A₀ : Subgroup Ω} {M : Type*} [Group M] (f : ↥A₀ →* M)
    (hcomm : ∀ a ∈ A₀, ∀ a' ∈ A₀, a * a' = a' * a) (hexp : ∀ a ∈ A₀, a ^ p = 1) :
    IsElemAbelian p f.range := by
  refine ⟨⟨⟨fun u v => ?_⟩⟩, fun φ hφ => ?_⟩
  · obtain ⟨a, ha⟩ := u.2
    obtain ⟨a', ha'⟩ := v.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← ha, ← ha', ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcomm _ a.2 _ a'.2)
  · obtain ⟨a, rfl⟩ := hφ
    rw [← map_pow]
    have : a ^ p = 1 := Subtype.ext (by simpa using hexp a a.2)
    rw [this, map_one]

theorem exists_decomp {p : ℕ} (hp : p.Prime) {A A₀ : Subgroup Ω} (hA₀A : A₀ ≤ A)
    (hcomm : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a) (hexp : ∀ a ∈ A, a ^ p = 1)
    (hcard : Nat.card A ≤ p * Nat.card A₀) {b : Ω} (hbA : b ∈ A) (hb : b ∉ A₀) :
    ∀ a ∈ A, ∃ a₀ ∈ A₀, ∃ k : ℤ, a = a₀ * b ^ k := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set A₀' : Subgroup ↥A := A₀.subgroupOf A with hA₀'
  haveI hN : A₀'.Normal := ⟨fun n hn g => by
    have : g * n * g⁻¹ = n := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hcomm _ g.2 _ n.2]
      group
    rw [this]
    exact hn⟩
  have hQ : Nat.card (↥A ⧸ A₀') ≤ p := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup A₀'
    have h2 : Nat.card A₀' = Nat.card A₀ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₀A).toEquiv
    rw [h2] at h1
    have hpos : 0 < Nat.card A₀ := Nat.card_pos
    rw [h1] at hcard
    exact Nat.le_of_mul_le_mul_right hcard hpos
  set bb : ↥A ⧸ A₀' := QuotientGroup.mk ⟨b, hbA⟩ with hbb
  have hbb1 : bb ≠ 1 := by
    intro h
    apply hb
    rw [hbb, QuotientGroup.eq_one_iff, hA₀', Subgroup.mem_subgroupOf] at h
    exact h
  have hbbp : bb ^ p = 1 := by
    rw [hbb, ← QuotientGroup.mk_pow]
    have : (⟨b, hbA⟩ : ↥A) ^ p = 1 := Subtype.ext (by simpa using hexp b hbA)
    rw [this, QuotientGroup.mk_one]
  have hord : orderOf bb = p := orderOf_eq_prime hbbp hbb1
  have htop : Subgroup.zpowers bb = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    apply le_antisymm (Subgroup.card_le_card_group _)
    rw [Nat.card_zpowers, hord]
    exact hQ
  intro a ha
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1
    (htop ▸ Subgroup.mem_top (QuotientGroup.mk ⟨a, ha⟩ : ↥A ⧸ A₀'))
  refine ⟨a * b ^ (-k), ?_, k, by group⟩
  have h1 : (QuotientGroup.mk (⟨a, ha⟩ * (⟨b, hbA⟩ : ↥A) ^ (-k)) : ↥A ⧸ A₀') = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_zpow, ← hbb, ← hk, ← zpow_add, add_neg_cancel,
      zpow_zero]
  rw [QuotientGroup.eq_one_iff, hA₀', Subgroup.mem_subgroupOf] at h1
  simpa using h1

theorem t156_core {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {S A A₀ : Subgroup Ω} {b : Ω}
    (hcore : GLAPPrimeCore p ↥S = ⊥) (hSc : GLAPComponent p S S)
    (hAN : A ≤ Subgroup.normalizer (S : Set Ω)) (hexp : ∀ a ∈ A, a ^ p = 1)
    (hcomm : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a) (hbA : b ∈ A) (hA₀A : A₀ ≤ A)
    (hdec : ∀ a ∈ A, ∃ a₀ ∈ A₀, ∃ k : ℤ, a = a₀ * b ^ k)
    (hbig : p ^ 2 * Nat.card ↥(A ⊓ centModSubgroup p S) ≤ Nat.card A₀)
    {R : Type} [Group R] (θ : PSimple p S ≃* R) {I : Set (MulAut R)}
    (hIinv : ∀ φ ∈ I, φ⁻¹ ∈ I)
    (hA₀I : ∀ a (ha : a ∈ A₀), MulAut.congr θ (indAut p S a (hAN (hA₀A ha))) ∈ I)
    (hFA : FixAlt p I (MulAut.congr θ (indAut p S b (hAN hbA)))) :
    Ipart p S b ≠ ⊥ ∧
      (∀ c ∈ A, CentMod p (Ipart p S b) c ↔
        c ∈ Subgroup.zpowers b ⊔ (A ⊓ centModSubgroup p S)) ∧
      InnDiagOn p A (Ipart p S b) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite R := Finite.of_equiv (PSimple p S) θ.toEquiv
  set C := A ⊓ centModSubgroup p S with hCdef
  have hbN : b ∈ Subgroup.normalizer (S : Set Ω) := hAN hbA
  have hbp : b ^ p = 1 := hexp b hbA
  set β := indAut p S b hbN with hβ
  set x := MulAut.congr θ β with hx
  have hαN : ∀ a ∈ A₀, a ∈ Subgroup.normalizer (S : Set Ω) := fun a ha => hAN (hA₀A ha)
  have hαx : ∀ a (ha : a ∈ A), MulAut.congr θ (indAut p S a (hAN ha)) * x =
      x * MulAut.congr θ (indAut p S a (hAN ha)) := by
    intro a ha
    have h3 : indAut p S (a * b) (Subgroup.mul_mem _ (hAN ha) hbN) =
        indAut p S (b * a) (Subgroup.mul_mem _ hbN (hAN ha)) := indAut_congr (hcomm a ha b hbA) _ _
    rw [indAut_mul (hAN ha) hbN, indAut_mul hbN (hAN ha)] at h3
    rw [hx, ← map_mul, ← map_mul, ← h3]
  have hαp : ∀ a (ha : a ∈ A), MulAut.congr θ (indAut p S a (hAN ha)) ^ p = 1 := by
    intro a ha
    rw [← map_pow, indAut_pow_eq_one (hAN ha) (hexp a ha), map_one]
  let ψA₀ : ↥A₀ →* MulAut R :=
    (OutCyc.psiHom p S θ).comp (Subgroup.inclusion (hA₀A.trans hAN))
  have hψα : ∀ a : ↥A₀, ψA₀ a = (MulAut.congr θ (indAut p S a (hαN a a.2)))⁻¹ := by
    intro a
    rw [OutCyc.indAut_eq_inv_chevAut, map_inv, inv_inv]
    rfl
  have hψI : ∀ a : ↥A₀, ψA₀ a ∈ I := fun a => by rw [hψα]; exact hIinv _ (hA₀I a a.2)
  have hψp : ∀ a : ↥A₀, ψA₀ a ^ p = 1 := fun a => by
    rw [hψα, inv_pow, hαp a (hA₀A a.2), inv_one]
  have hψx : ∀ a : ↥A₀, ψA₀ a * x = x * ψA₀ a := fun a => by
    rw [hψα]
    have h := hαx a (hA₀A a.2)
    calc (MulAut.congr θ (indAut p S ↑a (hαN a a.2)))⁻¹ * x
        = (MulAut.congr θ (indAut p S ↑a (hαN a a.2)))⁻¹ *
            (x * MulAut.congr θ (indAut p S ↑a (hαN a a.2))) *
            (MulAut.congr θ (indAut p S ↑a (hαN a a.2)))⁻¹ := by group
      _ = (MulAut.congr θ (indAut p S ↑a (hαN a a.2)))⁻¹ *
            (MulAut.congr θ (indAut p S ↑a (hαN a a.2)) * x) *
            (MulAut.congr θ (indAut p S ↑a (hαN a a.2)))⁻¹ := by rw [h]
      _ = x * (MulAut.congr θ (indAut p S ↑a (hαN a a.2)))⁻¹ := by group
  have hψker : ∀ a : ↥A₀, ψA₀ a = 1 → (a : Ω) ∈ C := by
    intro a h
    have h1 : chevAut p S ⟨a, hαN a a.2⟩ = 1 :=
      (MulAut.congr θ).injective (by rw [map_one]; exact h)
    exact ⟨hA₀A a.2, centMod_iff.1 ((chevAut_eq_one_iff hp hSc (hαN a a.2)).1 h1)⟩
  have hcommA₀ : ∀ a ∈ A₀, ∀ a' ∈ A₀, a * a' = a' * a := fun a ha a' ha' =>
    hcomm a (hA₀A ha) a' (hA₀A ha')
  have hexpA₀ : ∀ a ∈ A₀, a ^ p = 1 := fun a ha => hexp a (hA₀A ha)
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have hp2le : p < p ^ 2 := by nlinarith [hp.two_le]
  have hbig' : ∀ (M : Type) [Group M] (f : ↥A₀ →* M), (∀ a : ↥A₀, f a = 1 → (a : Ω) ∈ C) →
      p < Nat.card f.range := by
    intro M _ f hf
    have h1 := (hbig.trans (card_le_range_mul f hf))
    have h2 : p ^ 2 ≤ Nat.card f.range := Nat.le_of_mul_le_mul_right h1 hCpos
    omega
  rcases hFA with ⟨lab₀, hlab₀, hraw₀⟩ | hcyc
  swap
  · exfalso
    have h1 := hcyc ψA₀.range (isElemAbelian_range ψA₀ hcommA₀ hexpA₀)
      (fun φ hφ => by obtain ⟨a, rfl⟩ := hφ; exact ⟨hψI a, hψx a⟩)
    have h2 := hbig' _ ψA₀ hψker
    omega
  have hraw₁ := cAll_innRank hp hp2 hlab₀ _ hraw₀
  obtain ⟨R₀, _, I₀, F₀, ⟨hs₀, hna₀, θ₀, hFG⟩, hIR⟩ :=
    CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw₁
  haveI : Finite R₀ := Finite.of_equiv _ θ₀.toEquiv
  let Cx := Subgroup.centralizer ({x} : Set (MulAut R))
  let ψA₀' : ↥A₀ →* ↥Cx :=
    ψA₀.codRestrict Cx (fun a => Subgroup.mem_centralizer_singleton_iff.2 (hψx a))
  let r : ↥A₀ →* MulAut R₀ := (MulAut.congr θ₀).toMonoidHom.comp ((resHom x).comp ψA₀')
  have hr_apply : ∀ (a : ↥A₀) (g : ↥(ggFixDer x)),
      r a (θ₀ g) = θ₀ ⟨ψA₀ a g, ggFixDer_map_mem (hψx a) g.2⟩ := by
    intro a g
    show θ₀ ((resHom x (ψA₀' a)) (θ₀.symm (θ₀ g))) = _
    rw [MulEquiv.symm_apply_apply]
    rfl
  have hrI : ∀ a : ↥A₀, r a ∈ I₀ := by
    intro a
    obtain ⟨φ₀, hφ₀, hφ₀eq⟩ := hFG.1 (ψA₀ a) (hψI a) (hψp a) (hψx a)
    have he : r a = φ₀ := by
      ext y
      obtain ⟨g, rfl⟩ := θ₀.surjective y
      rw [hr_apply, ← hφ₀eq g g.2]
    rw [he]
    exact hφ₀
  have hrker : ∀ a : ↥A₀, r a = 1 → (a : Ω) ∈ C := by
    intro a h
    apply hψker a
    apply hFG.2 (ψA₀ a) (hψI a) (hψp a) (hψx a)
    intro g hg
    have h1 := hr_apply a ⟨g, hg⟩
    rw [h, MulAut.one_apply] at h1
    exact (congrArg Subtype.val (θ₀.injective h1)).symm
  obtain ⟨φ, hφE, hφ1, hφinn⟩ := hIR hs₀ hna₀ inferInstance r.range
    (isElemAbelian_range r hcommA₀ hexpA₀) (fun φ hφ => by obtain ⟨a, rfl⟩ := hφ; exact hrI a)
    (hbig' _ r hrker)
  obtain ⟨r₀, rfl⟩ := hφinn
  haveI := hs₀
  have hZ₀ : Subgroup.center R₀ = ⊥ := center_eq_bot_of_simple' hna₀
  have hr₀p : r₀ ^ p = 1 := by
    have h1 : (MulAut.conj r₀) ^ p = 1 := (isElemAbelian_range r hcommA₀ hexpA₀).2 _ hφE
    apply mulAut_conj_injective hZ₀
    rw [map_pow, h1, map_one]
  have hr₀1 : r₀ ≠ 1 := fun h => hφ1 (by rw [h, map_one])
  have hpR₀ : p ∣ Nat.card R₀ := by
    rw [← orderOf_eq_prime hr₀p hr₀1]
    exact orderOf_dvd_natCard r₀
  set E : Subgroup (PSimple p S) := ggFixDer β with hEdef
  have hθE : (ggFixDer β).map θ.toMonoidHom = ggFixDer x := (ggFixDer_congr θ β).symm
  let eSx : ↥E ≃* ↥(ggFixDer x) := (θ.subgroupMap E).trans (MulEquiv.subgroupCongr hθE)
  have heSx : ∀ e : ↥E, ((eSx e : ↥(ggFixDer x)) : R) = θ e := fun e => rfl
  let eS0 : ↥E ≃* R₀ := eSx.trans θ₀
  have hEs : IsSimpleGroup ↥E := (MulEquiv.isSimpleGroup_congr eS0).2 hs₀
  have hEna : ∃ u v : ↥E, u * v ≠ v * u := by
    obtain ⟨u, v, huv⟩ := hna₀
    exact ⟨eS0.symm u, eS0.symm v, fun h => huv (by simpa using congrArg eS0 h)⟩
  have hpE : p ∣ Nat.card ↥E := by
    rw [Nat.card_congr eS0.toEquiv]
    exact hpR₀
  have hfix : FP.fixSub β = ggFixSub β := by
    ext y
    exact Iff.rfl
  have hEle : E ≤ ggFixSub β := Subgroup.commutator_le.2 fun g hg h hh =>
    (ggFixSub β).mul_mem ((ggFixSub β).mul_mem ((ggFixSub β).mul_mem hg hh)
      ((ggFixSub β).inv_mem hg)) ((ggFixSub β).inv_mem hh)
  obtain ⟨hD1, hD2, -⟩ := FR.fieldOn_lift hp hp2 hbN hbp
  have hED : E ≤ ((S ⊓ Subgroup.centralizer ({b} : Set Ω)).subgroupOf S).map (chevQuotHom p S) := by
    rw [hEdef, ggFixDer, ← hfix]
    exact hD2
  have hEn : ∀ y ∈ ((S ⊓ Subgroup.centralizer ({b} : Set Ω)).subgroupOf S).map (chevQuotHom p S),
      ∀ e ∈ E, y * e * y⁻¹ ∈ E := by
    intro y hy e he
    have hyC : y ∈ ggFixSub β := hfix ▸ hD1 hy
    have hmap : (ggFixSub β).map (MulAut.conj y).toMonoidHom ≤ ggFixSub β := by
      rintro _ ⟨c, hc, rfl⟩
      exact (ggFixSub β).mul_mem ((ggFixSub β).mul_mem hyC hc) ((ggFixSub β).inv_mem hyC)
    have hEmap : E.map (MulAut.conj y).toMonoidHom ≤ E := by
      rw [hEdef, ggFixDer, Subgroup.map_commutator]
      exact Subgroup.commutator_mono hmap hmap
    exact hEmap ⟨e, he, by simp [MulAut.conj_apply]⟩
  obtain ⟨J, hJ, -⟩ := exists_pComponent_of_simple hp hcore hEs hEna hpE hED hEn
  have hEC : E ≤ fixSubgroup (chevAut p S ⟨b, hbN⟩) := by
    rw [← FR.fixSub_indAut hbN, hfix]
    exact hEle
  have hperf : ∀ T : Subgroup (PSimple p S), T ≤ fixSubgroup (chevAut p S ⟨b, hbN⟩) →
      ⁅T, T⁆ = T → T ≤ E := by
    intro T hT hTT
    rw [← FR.fixSub_indAut hbN, hfix] at hT
    rw [← hTT, hEdef, ggFixDer]
    exact Subgroup.commutator_mono hT hT
  have hI : Ipart p S b ≠ ⊥ := by
    intro h
    have hJle : J ≤ Ipart p S b := le_sSup hJ
    rw [h] at hJle
    exact glaPComponent_ne_bot' hJ (le_bot_iff.1 hJle)
  obtain ⟨J₀, hJ₀, hIJ₀, hJ₀T⟩ := FR.ipart_single hp hbN hbp hEs hEC hperf hI
  obtain ⟨Θ, hΘ⟩ := exists_pSimple_equiv hp hJ₀ inf_le_left hEs hEna hpE hJ₀T
  have hJ₀X : J₀ ≤ S ⊓ Subgroup.centralizer ({b} : Set Ω) := hJ₀.1
  have hπcore : ∀ (m : Ω) (hm : m ∈ GLAPPrimeCoreOf p J₀) (hmS : m ∈ S),
      chevQuotHom p S ⟨m, hmS⟩ = 1 := by
    intro m hm hmS
    obtain ⟨m', hm', rfl⟩ := hm
    have h1 := hΘ m'
    have h2 : (QuotientGroup.mk m' : PQuot p J₀) = 1 := (QuotientGroup.eq_one_iff _).2 hm'
    rw [h2, QuotientGroup.mk_one, map_one] at h1
    exact h1.symm.trans rfl
  have hπJ : ∀ (m : Ω) (hm : m ∈ J₀) (hmS : m ∈ S), chevQuotHom p S ⟨m, hmS⟩ ∈ E := by
    intro m hm hmS
    rw [← hJ₀T]
    exact ⟨⟨m, hmS⟩, Subgroup.mem_subgroupOf.2 hm, rfl⟩
  have hEπ : ∀ e ∈ E, ∃ (m : Ω) (hm : m ∈ J₀) (hmS : m ∈ S), chevQuotHom p S ⟨m, hmS⟩ = e := by
    intro e he
    rw [← hJ₀T] at he
    obtain ⟨s, hs, rfl⟩ := he
    exact ⟨s, Subgroup.mem_subgroupOf.1 hs, s.2, rfl⟩
  have hind : ∀ (a : Ω) (ha : a ∈ Subgroup.normalizer (S : Set Ω)) (m : Ω) (hmS : m ∈ S)
      (hm' : a⁻¹ * m * a ∈ S),
      indAut p S a ha (chevQuotHom p S ⟨m, hmS⟩) = chevQuotHom p S ⟨a⁻¹ * m * a, hm'⟩ := by
    intro a ha m hmS hm'
    exact indAut_apply_mk ha ⟨⟨m, hmS⟩, ⟨a⁻¹ * m * a, hm'⟩, rfl, rfl, rfl⟩
  rw [hIJ₀]
  refine ⟨glaPComponent_ne_bot' hJ₀, ?_, ?_⟩
  ·
    intro c hc
    constructor
    · intro hcm
      obtain ⟨a₀, ha₀, k, rfl⟩ := hdec c hc
      have hcN : a₀ * b ^ k ∈ Subgroup.normalizer (S : Set Ω) := hAN hc
      have hfixE : ∀ e ∈ E, indAut p S (a₀ * b ^ k) hcN e = e := by
        intro e he
        obtain ⟨m, hm, hmS, rfl⟩ := hEπ e he
        have hcinv : (a₀ * b ^ k)⁻¹ ∈ centModSubgroup p J₀ :=
          (centModSubgroup p J₀).inv_mem (centMod_iff.1 hcm)
        have hk1 := (mem_centModSubgroup.1 hcinv).2 m hm
        have hcm1 : (a₀ * b ^ k)⁻¹⁻¹ * m⁻¹ * (a₀ * b ^ k)⁻¹ ∈ S := by
          have := (Subgroup.mem_normalizer_iff.1 hcN m⁻¹).1 (S.inv_mem hmS)
          simpa using this
        have hcm2 : (a₀ * b ^ k)⁻¹ * m * (a₀ * b ^ k) ∈ S := by
          have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hcN) m).1 hmS
          simpa using this
        have hcm3 : (a₀ * b ^ k)⁻¹ * m⁻¹ * (a₀ * b ^ k) ∈ S := by
          have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hcN) m⁻¹).1 (S.inv_mem hmS)
          simpa using this
        have hcomS : ⁅m, (a₀ * b ^ k)⁻¹⁆ ∈ S := by
          rw [commutatorElement_def]
          have : m * (a₀ * b ^ k)⁻¹ * m⁻¹ * (a₀ * b ^ k)⁻¹⁻¹ =
              m * ((a₀ * b ^ k)⁻¹ * m⁻¹ * (a₀ * b ^ k)) := by group
          rw [this]
          exact S.mul_mem hmS hcm3
        have h1 : chevQuotHom p S ⟨⁅m, (a₀ * b ^ k)⁻¹⁆, hcomS⟩ = 1 := hπcore _ hk1 hcomS
        have h2 : (⟨⁅m, (a₀ * b ^ k)⁻¹⁆, hcomS⟩ : ↥S) =
            ⟨m, hmS⟩ * (⟨(a₀ * b ^ k)⁻¹ * m * (a₀ * b ^ k), hcm2⟩ : ↥S)⁻¹ := by
          apply Subtype.ext
          simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
          group
        rw [h2, map_mul, map_inv, mul_inv_eq_one] at h1
        rw [hind (a₀ * b ^ k) hcN m hmS hcm2]
        exact h1.symm
      have hβfix : ∀ e ∈ E, ∀ j : ℤ, (β ^ j) e = e := by
        intro e he j
        have hβe : β e = e := hEle he
        induction j using Int.induction_on with
        | zero => simp
        | succ i ih => rw [zpow_add_one, MulAut.mul_apply, hβe, ih]
        | pred i ih =>
          have hβe' : β⁻¹ e = e := by
            conv_lhs => rw [← hβe]
            simp
          rw [zpow_sub_one, MulAut.mul_apply, hβe', ih]
      have hbkN : b ^ k ∈ Subgroup.normalizer (S : Set Ω) := Subgroup.zpow_mem _ hbN k
      have hsplit : indAut p S (a₀ * b ^ k) hcN = β ^ k * indAut p S a₀ (hαN a₀ ha₀) := by
        rw [indAut_congr rfl hcN (Subgroup.mul_mem _ (hαN a₀ ha₀) hbkN),
          indAut_mul (hαN a₀ ha₀) hbkN, indAut_congr rfl hbkN (Subgroup.zpow_mem _ hbN k),
          indAut_zpow hbN k]
      have hfix₀ : ∀ e ∈ E, indAut p S a₀ (hαN a₀ ha₀) e = e := by
        intro e he
        have h1 := hfixE e he
        rw [hsplit, MulAut.mul_apply] at h1
        have h2 := congrArg (β ^ (-k)) h1
        rw [← MulAut.mul_apply, ← zpow_add, neg_add_cancel, zpow_zero, MulAut.one_apply,
          hβfix e he] at h2
        exact h2
      have hfixx : ∀ g ∈ ggFixDer x, MulAut.congr θ (indAut p S a₀ (hαN a₀ ha₀)) g = g := by
        intro g hg
        rw [← hθE] at hg
        obtain ⟨e, he, rfl⟩ := hg
        show θ (indAut p S a₀ (hαN a₀ ha₀) (θ.symm (θ e))) = θ e
        rw [MulEquiv.symm_apply_apply, hfix₀ e he]
      have hα1 := hFG.2 _ (hA₀I a₀ ha₀) (hαp a₀ (hA₀A ha₀)) (hαx a₀ (hA₀A ha₀)) hfixx
      have hind1 : indAut p S a₀ (hαN a₀ ha₀) = 1 :=
        (MulAut.congr θ).injective (by rw [hα1, map_one])
      have hchev1 : chevAut p S ⟨a₀, hαN a₀ ha₀⟩ = 1 := by
        rw [OutCyc.indAut_eq_inv_chevAut, inv_eq_one] at hind1
        exact hind1
      have ha₀C : a₀ ∈ centModSubgroup p S :=
        centMod_iff.1 ((chevAut_eq_one_iff hp hSc (hαN a₀ ha₀)).1 hchev1)
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨hA₀A ha₀, ha₀C⟩)
        (Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers b k))
    · intro hcm
      apply centMod_of_mem_centralizer
      have h1 : Subgroup.zpowers b ≤ Subgroup.centralizer (J₀ : Set Ω) := by
        rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        intro j hj
        exact Subgroup.mem_centralizer_singleton_iff.1 (hJ₀X hj).2
      have h2 : A ⊓ centModSubgroup p S ≤ Subgroup.centralizer (J₀ : Set Ω) := by
        intro z hz
        rw [Subgroup.mem_centralizer_iff]
        intro j hj
        have h3 := (mem_centModSubgroup.1 hz.2).2 j (hJ₀X hj).1
        rw [glaPPrimeCoreOf_eq_bot_p hcore, Subgroup.mem_bot,
          commutatorElement_eq_one_iff_mul_comm] at h3
        exact h3
      exact (sup_le h1 h2) hcm
  ·
    have hAJ : A ≤ Subgroup.normalizer (J₀ : Set Ω) := by
      intro a ha
      have h1 := normalizes_inf_centralizer_singleton (hAN ha) (hcomm a ha b hbA)
      have h2 := normalizes_glaPLayer (p := p) h1
      rw [← hIJ₀]
      exact h2
    refine ⟨hAJ, ?_⟩
    have hq₀ := isQuasisimple_pQuot_of_glaPComponent hp hJ₀
    refine ⟨hq₀.1, lab₀, hlab₀, Canonical.largeEvenRawDatum_mono ?_ hraw₀⟩
    rintro R₀' _ I₀' F₀' ⟨hs', hna', θ₀', hFG'⟩
    refine ⟨hs', hna', Θ.trans (eSx.trans θ₀'), ?_⟩
    intro a ha
    obtain ⟨a₀, ha₀, k, rfl⟩ := hdec a ha
    obtain ⟨φ₀, hφ₀, hφ₀eq⟩ := hFG'.1 _ (hA₀I a₀ ha₀) (hαp a₀ (hA₀A ha₀)) (hαx a₀ (hA₀A ha₀))
    refine ⟨φ₀, hφ₀, ?_⟩
    rintro l l' ⟨m, m', rfl, rfl, hmm'⟩
    have hmS : (m : Ω) ∈ S := (hJ₀X m.2).1
    have hm'S : (m' : Ω) ∈ S := (hJ₀X m'.2).1
    have hmem : a₀⁻¹ * (m : Ω) * a₀ ∈ J₀ := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ (hAJ (hA₀A ha₀))) m).1 m.2
      simpa using this
    have hcb : (a₀⁻¹ * (m : Ω) * a₀) * b ^ k = b ^ k * (a₀⁻¹ * (m : Ω) * a₀) := by
      have hb' : b ^ k ∈ Subgroup.centralizer ({a₀⁻¹ * (m : Ω) * a₀} : Set Ω) := by
        apply Subgroup.zpow_mem
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.1 (hJ₀X hmem).2).symm
      exact (Subgroup.mem_centralizer_singleton_iff.1 hb').symm
    have hm'eq : (m' : Ω) = a₀⁻¹ * m * a₀ := by
      rw [hmm']
      calc (a₀ * b ^ k)⁻¹ * (m : Ω) * (a₀ * b ^ k)
          = (b ^ k)⁻¹ * ((a₀⁻¹ * (m : Ω) * a₀) * b ^ k) := by group
        _ = (b ^ k)⁻¹ * (b ^ k * (a₀⁻¹ * (m : Ω) * a₀)) := by rw [hcb]
        _ = a₀⁻¹ * m * a₀ := by group
    have hm₀S : a₀⁻¹ * (m : Ω) * a₀ ∈ S := hm'eq ▸ hm'S
    have hkey : MulAut.congr θ (indAut p S a₀ (hαN a₀ ha₀)) (θ (chevQuotHom p S ⟨m, hmS⟩)) =
        θ (chevQuotHom p S ⟨m', hm'S⟩) := by
      show θ (indAut p S a₀ (hαN a₀ ha₀) (θ.symm (θ (chevQuotHom p S ⟨m, hmS⟩)))) = _
      rw [MulEquiv.symm_apply_apply, hind a₀ (hαN a₀ ha₀) m hmS hm₀S]
      congr 2
      exact Subtype.ext hm'eq.symm
    have hmemx : ∀ (y : Ω) (hy : y ∈ J₀) (hyS : y ∈ S), θ (chevQuotHom p S ⟨y, hyS⟩) ∈ ggFixDer x := by
      intro y hy hyS
      rw [← hθE]
      exact ⟨_, hπJ y hy hyS, rfl⟩
    have hθ' : ∀ (y : ↥J₀) (hyS : (y : Ω) ∈ S),
        (Θ.trans (eSx.trans θ₀')) (QuotientGroup.mk (QuotientGroup.mk y : PQuot p J₀)) =
          θ₀' ⟨θ (chevQuotHom p S ⟨y, hyS⟩), hmemx y y.2 hyS⟩ := by
      intro y hyS
      rw [MulEquiv.trans_apply, MulEquiv.trans_apply]
      congr 1
      apply Subtype.ext
      rw [heSx, hΘ y]
    rw [hθ' m hmS, hθ' m' hm'S, ← hφ₀eq _ (hmemx m m.2 hmS)]
    congr 1
    exact Subtype.ext hkey

theorem t156FactOmega_of_geom (hG : T156Geom) (p : ℕ) : T156FactOmega p := by
  intro hp hp2 Ω _ _ S A b _ hSq hcore hchev hAN hAel hbA hR2 hG2 hrank hnt
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hbN : b ∈ Subgroup.normalizer (S : Set Ω) := hAN hbA
  have hexp : ∀ a ∈ A, a ^ p = 1 := hAel.2
  have hcomm : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a := fun a ha a' ha' =>
    congrArg Subtype.val (hAel.1.is_comm.comm ⟨a, ha⟩ ⟨a', ha'⟩)
  have eP : PQuot p S ≃* ↥S :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot
  have hq : CFSG.Open.IsQuasisimple (PQuot p S) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv eP.symm hSq
  have hSc : GLAPComponent p S S := glaPComponent_self_p hSq hcore
  obtain ⟨A₀, hA₀A, hA₀inn, hcard, hA₀max⟩ := t156_split hp hp2 hq hchev hAN hexp hnt
  have hbA₀ : b ∉ A₀ := by
    intro hb
    have hD : InnDiagOn p (Subgroup.zpowers b) S := innDiagOn_mono (Subgroup.zpowers_le.2 hb) hA₀inn
    rcases hR2 with hF | ⟨rfl, hTD4, hNI⟩
    · exact (field_nonInnDiag_holds hp hp2 hF).2 hD
    · exact (td4_nonInnDiag_holds hp hSc hTD4 hNI).2 hD
  have hCA₀ : A ⊓ centModSubgroup p S ≤ A₀ := by
    intro c hc
    have hcN := hAN hc.1
    apply hA₀max c hc.1
    have h1 : chevAut p S ⟨c, hcN⟩ = 1 := (chevAut_eq_one_iff hp hSc hcN).2 (centMod_iff.2 hc.2)
    have h2 : indAut p S c hcN = 1 := by rw [OutCyc.indAut_eq_inv_chevAut, h1, inv_one]
    have hin : InducesInnerMod p S c :=
      (indAut_mem_inner_iff hp hSc hcN).1 (h2 ▸ Subgroup.one_mem _)
    exact inner_innDiag_holds hp hSc hchev hcN hin
  have hbig : p ^ 2 * Nat.card ↥(A ⊓ centModSubgroup p S) ≤ Nat.card A₀ := by
    have h1 : p * (p ^ 2 * Nat.card ↥(A ⊓ centModSubgroup p S)) ≤ p * Nat.card A₀ := by
      calc p * (p ^ 2 * Nat.card ↥(A ⊓ centModSubgroup p S))
          = p ^ 3 * Nat.card ↥(A ⊓ centModSubgroup p S) := by ring
        _ ≤ Nat.card A := hrank
        _ ≤ p * Nat.card A₀ := hcard
    exact Nat.le_of_mul_le_mul_left h1 hp.pos
  have hdec := exists_decomp hp hA₀A hcomm hexp hcard hbA hbA₀
  have h₁ : ∀ a ∈ (A₀ : Set Ω), CFSG.Assembly.LargeEvenMarking (PQuot p S) fun _ _ _ I _ θ =>
      ∃ φ ∈ I, LargeEvenInduces θ (indRel p S a) φ := fun a ha =>
    Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ hh => hh a ha) hA₀inn.2
  have hall : ∀ lab, LargeEvenInLambda2 lab → MI.CAll lab (LargeEvenSimpleGuard
      (fun R _ I F => GeomBody p lab R I F ∧ MI.RawInnBody p R I F)) := fun lab hlab =>
    MI.CAll.mono (fun R _ I F h hs hna => ⟨h.1, h.2 hs hna⟩)
      (MI.CAll.and (hG p hp hp2 lab hlab) (MI.canonRawInn' hp hp2 hlab))
  have hA₀I_of : ∀ {R : Type} [Group R] {I : Set (MulAut R)}
      (θ : PQuot p S ⧸ Subgroup.center (PQuot p S) ≃* R),
      (∀ a ∈ (A₀ : Set Ω), ∃ φ ∈ I, LargeEvenInduces θ (indRel p S a) φ) →
      ∀ a (ha : a ∈ A₀), MulAut.congr θ (indAut p S a (hAN (hA₀A ha))) ∈ I := by
    intro R _ I θ h a ha
    obtain ⟨φ, hφ, hind⟩ := h a ha
    rw [← (induces_indRel_iff (hAN (hA₀A ha)) θ).1 hind]
    exact hφ
  rcases hR2 with hF | ⟨rfl, hTD4, hNI⟩
  ·
    have hM := MI.marking_transport_family (fun a : Ω => indRel p S a) (A₀ : Set Ω)
      (Set.toFinite _) h₁ hF.2
    have hM' := FP.canon_marking_and_labelAll_simple'
      (P' := fun lab R _ I F => GeomBody p lab R I F ∧ MI.RawInnBody p R I F) hall hM
    obtain ⟨-, lab, hlab, R, _, I, F, θ, hs, hna, ⟨hPF, hA₀P⟩, hGB, hRaw⟩ :=
      Canonical.largeEvenMarking_exists hM'
    obtain ⟨hne, f, hf, u, hu, hord, hind⟩ := hPF
    have hx : MulAut.congr θ (indAut p S b hbN) = u * f * u⁻¹ :=
      ((induces_indRel_iff hbN θ).1 hind).symm
    have hne' : ¬ (lab.tag = .triD4 ∧ p = 3) := by
      rintro ⟨h1, h2⟩
      rcases hne with h | h
      · exact h h1
      · exact h h2
    rcases (hGB hs hna).1 hne' f hf hord with hFA | ⟨h3, hU⟩
    · left
      have hFA' : FixAlt p I (MulAut.congr θ (indAut p S b hbN)) := by
        rw [hx]
        exact fixAlt_conj (J := OutCyc.rawSubgroup hRaw) hu hFA
      exact t156_core hp hp2 hcore hSc hAN hexp hcomm hbA hA₀A hdec hbig θ hRaw.2.1
        (hA₀I_of θ hA₀P) hFA'
    · right
      subst h3
      exact ⟨rfl, (catalogIs_congr θ).2 hU⟩
  ·
    have M₀ := Canonical.largeEvenMarking_markedModel
      (CFSG.StandardType.ChevTwo.ys08_holds (PQuot 3 S) hq hchev)
    have hM := MI.marking_transport_family (fun a : Ω => indRel 3 S a) (A₀ : Set Ω)
      (Set.toFinite _) h₁ M₀
    have hM' := FP.canon_marking_and_labelAll_simple'
      (P' := fun lab R _ I F => GeomBody 3 lab R I F ∧ MI.RawInnBody 3 R I F) hall hM
    obtain ⟨-, lab, hlab, R, _, I, F, θ, hs, hna, ⟨⟨-, hMM⟩, hA₀P⟩, hGB, hRaw⟩ :=
      Canonical.largeEvenMarking_exists hM'
    haveI : Finite R := Finite.of_equiv (PSimple 3 S) θ.toEquiv
    have htag : lab.tag = .triD4 := tag_triD4_of_isTD4 hMM hTD4 θ
    have hx3 : MulAut.congr θ (indAut 3 S b hbN) ^ 3 = 1 := by
      rw [← map_pow, indAut_pow_eq_one hbN (hexp b hbA), map_one]
    have hxni : MulAut.congr θ (indAut 3 S b hbN) ∉ (MulAut.conj : R →* MulAut R).range := by
      rintro ⟨r, hr⟩
      apply hNI.2
      apply (indAut_mem_inner_iff hp hSc hbN).1
      refine ⟨θ.symm r, ?_⟩
      apply (MulAut.congr θ).injective
      rw [MI.congr_conj, MulEquiv.apply_symm_apply, hr]
    have hx2 : S10.twoPart (FP.fixNum (MulAut.congr θ (indAut 3 S b hbN))) =
        Nat.sqrt (S10.twoPart (Nat.card R)) := by
      have h1 := hG2 rfl hTD4
      rw [FP.centCard2_eq_twoPart_fixNum hbN (FP.odd_card_center_pQuot hp hp2 S),
        FP.card2_eq_twoPart_card_pSimple hp hp2 S] at h1
      rw [FP.fixNum_congr, h1, Nat.card_congr θ.toEquiv]
    have hFA := (hGB hs hna).2 htag rfl _ hx3 hxni hx2
    left
    exact t156_core hp hp2 hcore hSc hAN hexp hcomm hbA hA₀A hdec hbig θ hRaw.2.1
      (hA₀I_of θ hA₀P) hFA

theorem t156FactOmega_of_rest (h : T156Rest) (p : ℕ) : T156FactOmega p :=
  t156FactOmega_of_geom (t156Geom_of_rest h) p

end Core

end CFSG.LocalAnalysis.GLTheoremA.T156

end
