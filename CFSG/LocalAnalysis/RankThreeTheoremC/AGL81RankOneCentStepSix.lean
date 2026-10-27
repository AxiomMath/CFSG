module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.PLengthLemmas
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.AGLEmbedding.NongenerationTransfer
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent

open CFSG.AGLEmbedding CFSG.Open

@[expose] def IsLinUnitThreeEven (Y : Type) [Group Y] : Prop :=
  ∃ (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower), q.p = 2 ∧
    (d.1 = .A 2 q ∨ d.1 = .twistedA 2 q) ∧ Nonempty (Y ≃* (TauCeti.CFSGIndex.lie d).Group)

@[expose] def KFactCentralThreeClassical : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], Open.IsQuasisimple Y →
    IsClassicalTwoOrG2 (Y ⧸ Subgroup.center Y) → 3 ∣ Nat.card (Subgroup.center Y) →
    Nonempty (Y ⧸ Subgroup.center Y ≃* alternatingGroup (Fin 6)) ∨
      4 ≤ Open.pRank 3 (⊤ : Subgroup Y) ∨ IsLinUnitThreeEven (Y ⧸ Subgroup.center Y)

@[expose] def KFactAltSixFixed : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], Open.IsQuasisimple Y →
    Nonempty (Y ⧸ Subgroup.center Y ≃* alternatingGroup (Fin 6)) →
    ∀ (φ : MulAut Y) (n : ℕ), φ ^ (3 ^ n) = 1 → φ ≠ 1 →
      HasNormalPComplement 3 ↥(φ.toMonoidHom.eqLocus (MonoidHom.id Y))

@[expose] def KFactLinUnitThreeParabolic : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Y P R : Subgroup X), Open.IsQuasisimple ↥Y →
    IsLinUnitThreeEven (↥Y ⧸ Subgroup.center ↥Y) → 3 ∣ Nat.card (Subgroup.center ↥Y) →
    IsParabolicTwo Y P → R ≤ P →
    Open.IsSubnormal R P → IsEmpty (↥R ⧸ CFSG.pCore 2 ↥R ≃* Equiv.Perm (Fin 3))

section Quot

variable {X : Type} [Group X] [Finite X]

@[expose] def conjOn (Y : Subgroup X) {a : X} (ha : a ∈ Subgroup.normalizer (Y : Set X)) :
    MulAut ↥Y where
  toFun y := ⟨a * y * a⁻¹, (Subgroup.mem_normalizer_iff.mp ha y).mp y.2⟩
  invFun y := ⟨a⁻¹ * y * a, (Subgroup.mem_normalizer_iff.mp ha (a⁻¹ * y * a)).mpr (by
    have e : a * (a⁻¹ * (y : X) * a) * a⁻¹ = y := by group
    rw [e]
    exact y.2)⟩
  left_inv y := Subtype.ext (by simp [mul_assoc])
  right_inv y := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by
    change a * ((x : X) * y) * a⁻¹ = a * x * a⁻¹ * (a * y * a⁻¹)
    group)

theorem conjOn_apply (Y : Subgroup X) {a : X} (ha : a ∈ Subgroup.normalizer (Y : Set X))
    (y : Y) : ((conjOn Y ha y : Y) : X) = a * y * a⁻¹ := rfl

theorem conjOn_pow (Y : Subgroup X) {a : X} (ha : a ∈ Subgroup.normalizer (Y : Set X))
    (n : ℕ) (y : Y) : (((conjOn Y ha ^ n) y : Y) : X) = a ^ n * y * (a ^ n)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply, conjOn_apply, ih]
    group

theorem false_of_stepSix_quot (hKC : KFactCentralThreeClassical) (hKA : KFactAltSixFixed)
    (hKL : KFactLinUnitThreeParabolic) {Y P R J : Subgroup X} {a : X} (hY : Open.IsQuasisimple ↥Y)
    (hcl : IsClassicalTwoOrG2 (↥Y ⧸ Subgroup.center ↥Y))
    (h3Z : 3 ∣ Nat.card (Subgroup.center ↥Y)) (hpar : IsParabolicTwo Y P)
    (hX3 : Open.pRank 3 (⊤ : Subgroup X) ≤ 3) (haY : a ∈ Subgroup.normalizer (Y : Set X))
    (ha3 : a ^ 3 = 1) (hal : ∃ l ∈ Y, a * l * a⁻¹ ≠ l) (hJY : J ≤ Y)
    (hJa : ∀ x ∈ J, a * x = x * a) (hJ : ¬ HasNormalPComplement 3 ↥J) (hRP : R ≤ P)
    (hRs : Open.IsSubnormal R P) (hR : Nonempty (↥R ⧸ CFSG.pCore 2 ↥R ≃* Equiv.Perm (Fin 3))) :
    False := by
  rcases hKC ↥Y hY hcl h3Z with hA6 | h4 | hLU
  ·
    set φ := conjOn Y haY
    have hφ3 : φ ^ (3 ^ 1) = 1 := by
      ext y
      rw [conjOn_pow, pow_one, ha3]
      simp
    have hφ1 : φ ≠ 1 := by
      obtain ⟨l, hl, hne⟩ := hal
      intro h
      apply hne
      have := congrArg (fun ψ : MulAut ↥Y => ((ψ ⟨l, hl⟩ : Y) : X)) h
      simpa [φ, conjOn_apply] using this
    have hF := hKA ↥Y hY hA6 φ 1 hφ3 hφ1
    have hle : J.subgroupOf Y ≤ φ.toMonoidHom.eqLocus (MonoidHom.id ↥Y) := by
      intro y hy
      refine Subtype.ext ?_
      change a * (y : X) * a⁻¹ = y
      rw [hJa y hy]
      group
    exact hJ (hasNormalPComplement_of_equiv 3 (Subgroup.subgroupOfEquivOfLe hJY)
      (hasNormalPComplement_of_le 3 hle hF))
  ·
    have h1 := CFSG.SectionRank.pRank_le_map (p := 3) (by norm_num) Y.subtype
      Y.subtype_injective ⊤
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
    have h2 := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) (le_top : Y ≤ ⊤)
    omega
  ·
    exact (hKL X Y P R hY hLU h3Z hpar hRP hRs).false hR.some

end Quot

variable {G : Type} [Group G] [Finite G]

theorem nonempty_quotPCore_mulEquiv {A A' : Type*} [Group A] [Group A'] {p : ℕ} [Fact p.Prime]
    (f : A →* A') (hf : Function.Surjective f) (hker : IsPGroup p f.ker) :
    Nonempty (A ⧸ CFSG.pCore p A ≃* A' ⧸ CFSG.pCore p A') := by
  have hcomap : (CFSG.pCore p A').comap f = CFSG.pCore p A := by
    apply le_antisymm
    · exact le_sSup ⟨(CFSG.pCore_normal (p := p) (G := A')).comap f,
        (CFSG.pCore_isPGroup (p := p) (G := A')).comap_of_ker_isPGroup f hker⟩
    · intro x hx
      have hle : (CFSG.pCore p A).map f ≤ CFSG.pCore p A' :=
        le_sSup ⟨(CFSG.pCore_normal (p := p) (G := A)).map f hf,
          (CFSG.pCore_isPGroup (p := p) (G := A)).map f⟩
      exact hle ⟨x, hx, rfl⟩
  have hsurj : Function.Surjective ((QuotientGroup.mk' (CFSG.pCore p A')).comp f) :=
    (QuotientGroup.mk'_surjective _).comp hf
  have hk : CFSG.pCore p A = ((QuotientGroup.mk' (CFSG.pCore p A')).comp f).ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', hcomap]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hk).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ hsurj)⟩

theorem false_of_stepSix (hKC : KFactCentralThreeClassical) (hKA : KFactAltSixFixed)
    (hKL : KFactLinUnitThreeParabolic) {M L H I J : Subgroup G} {a : G}
    (hLc : Open.IsComponentOf (barM M L) ⊤) (hLM : L ≤ M) (hLn : (L.subgroupOf M).Normal)
    (hcl : IsClassicalTwoOrG2 (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)))
    (hpar : IsParabolicTwo (barM M L) (barM M (H ⊓ L)))
    (h3Z : 3 ∣ Nat.card (Subgroup.center ↥(barM M L))) (hM3 : Open.pRank 3 M ≤ 3)
    (haM : a ∈ M) (ha3 : a ^ 3 = 1) (haL : ¬ ∀ l ∈ L, a * l * a⁻¹ * l⁻¹ ∈ pCoreOf 2 M)
    (hJL : J ≤ L) (hJa : ∀ x ∈ J, a * x = x * a) (hJ : ¬ HasNormalPComplement 3 ↥(barM M J))
    (hIHL : I ≤ H ⊓ L) (hIs : Open.IsSubnormal I (H ⊓ L))
    (hI : Nonempty (↥I ⧸ CFSG.pCore 2 ↥I ≃* Equiv.Perm (Fin 3))) : False := by
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  set a' : ↥M := ⟨a, haM⟩
  have hX3 : Open.pRank 3 (⊤ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) ≤ 3 := by
    have hcop : (3 : ℕ).Coprime (Nat.card (CFSG.pCore 2 ↥M)) := by
      obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥M)).exists_card_eq
      rw [hn]
      exact Nat.Coprime.pow_right _ (by norm_num)
    have h := pRank_map_mk_eq_pRank_map_subtype (p := 3) Nat.prime_three (CFSG.pCore 2 ↥M)
      hcop ⊤
    rw [← MonoidHom.range_eq_map, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
      MonoidHom.range_eq_top.mpr hπs] at h
    rw [h]
    exact hM3
  have hLbn : (barM M L).Normal := hLn.map π hπs
  have haY : π a' ∈ Subgroup.normalizer ((barM M L : Subgroup _) : Set _) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hLbn.conj_mem h hh (π a')
    · intro hh
      have := hLbn.conj_mem _ hh (π a')⁻¹
      simpa [mul_assoc] using this
  have ha3' : π a' ^ 3 = 1 := by
    rw [← map_pow]
    have : a' ^ 3 = 1 := Subtype.ext (by simpa [a'] using ha3)
    rw [this, map_one]
  have hal : ∃ l ∈ barM M L, π a' * l * (π a')⁻¹ ≠ l := by
    push Not at haL
    obtain ⟨l, hl, hnot⟩ := haL
    refine ⟨π ⟨l, hLM hl⟩, ⟨⟨l, hLM hl⟩, hl, rfl⟩, fun h => hnot ?_⟩
    have h1 : π (a' * ⟨l, hLM hl⟩ * a'⁻¹ * (⟨l, hLM hl⟩ : ↥M)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, h, mul_inv_cancel]
    have h2 := (QuotientGroup.eq_one_iff _).mp h1
    exact ⟨_, h2, rfl⟩
  have hJY : barM M J ≤ barM M L := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hJL hx, rfl⟩
  have hJa' : ∀ x ∈ barM M J, π a' * x = x * π a' := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg π (Subtype.ext (hJa x hx))
  have hIM : I ≤ M := hIHL.trans (inf_le_right.trans hLM)
  have hRP : barM M I ≤ barM M (H ⊓ L) := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hIHL hx, rfl⟩
  have hRs : Open.IsSubnormal (barM M I) (barM M (H ⊓ L)) :=
    CFSG.Open.IsSubnormal.map π (CFSG.Open.IsSubnormal.comap M.subtype hIs)
  set f : ↥I →* ↥M ⧸ CFSG.pCore 2 ↥M := π.comp (Subgroup.inclusion hIM) with hf
  have hfr : f.range = barM M I := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨Subgroup.inclusion hIM i, i.2, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨m, hm⟩, rfl⟩
  have hfk : IsPGroup 2 f.ker := by
    rw [hf, ← MonoidHom.comap_ker, hπ, QuotientGroup.ker_mk']
    exact (CFSG.pCore_isPGroup (p := 2) (G := ↥M)).comap_of_injective _
      (Subgroup.inclusion_injective hIM)
  obtain ⟨e⟩ := nonempty_quotPCore_mulEquiv (p := 2) f.rangeRestrict f.rangeRestrict_surjective
    (by rw [MonoidHom.ker_rangeRestrict]; exact hfk)
  have hR : Nonempty (↥(barM M I) ⧸ CFSG.pCore 2 ↥(barM M I) ≃* Equiv.Perm (Fin 3)) := by
    rw [← hfr]
    exact ⟨e.symm.trans hI.some⟩
  exact false_of_stepSix_quot hKC hKA hKL hLc.2.2 hcl h3Z hpar hX3 haY ha3' hal hJY hJa' hJ
    hRP hRs hR

end CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent
