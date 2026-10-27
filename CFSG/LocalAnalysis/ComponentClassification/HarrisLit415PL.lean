module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415PBase
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndLift
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndRank
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitBlowup
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.TwoA.Census.PermClasses

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd

namespace L415

theorem isPComponent_barOf {X : Type} [Group X] [Finite X] {m b : X}
    (hbm : b ∈ centralizer ({m} : Set X)) (hb : orderOf b = 2) {J : Subgroup X}
    (hJ : IsTwoComponentIn J (centralizer {m} ⊓ centralizer {b})) :
    barOf (centralizer {m}) J ≤ centralizer {(QuotientGroup.mk ⟨b, hbm⟩ : MBar m)} ∧
      IsPComponent 2 ((barOf (centralizer {m}) J).subgroupOf
        (centralizer {(QuotientGroup.mk ⟨b, hbm⟩ : MBar m)})) ∧
      Nonempty (↥J ⧸ pPrimeCore 2 ↥J ≃* ↥(barOf (centralizer {m}) J) ⧸
        pPrimeCore 2 ↥(barOf (centralizer {m}) J)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let M := centralizer ({m} : Set X)
  let b' : ↥M := ⟨b, hbm⟩
  let π := QuotientGroup.mk' (pPrimeCore 2 ↥M)
  let C := centralizer ({b'} : Set ↥M)
  have hb'2 : b' * b' = 1 := Subtype.ext (by
    change b * b = 1
    rw [← sq, ← hb, pow_orderOf_eq_one])
  have hodd : Odd (Nat.card (pPrimeCore 2 ↥M)) := by
    have h2 := GSThmB.OddQuot.not_two_dvd_card_ker (H := ↥M)
    rw [QuotientGroup.ker_mk'] at h2
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h2)
  have hCmap : C.map π = centralizer {(QuotientGroup.mk ⟨b, hbm⟩ : MBar m)} :=
    map_centralizer_eq hodd hb'2
  let φ : ↥C →* ↥(centralizer ({(QuotientGroup.mk ⟨b, hbm⟩ : MBar m)} : Set (MBar m))) :=
    (π.comp C.subtype).codRestrict _ (fun x => hCmap ▸ mem_map_of_mem π x.2)
  have hφs : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    rw [← hCmap] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hφk : ¬ 2 ∣ Nat.card φ.ker := by
    have hle : φ.ker.map C.subtype ≤ pPrimeCore 2 ↥M := by
      rintro _ ⟨x, hx, rfl⟩
      have hx' : π (x : ↥M) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      rwa [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at hx'
    have hc : Nat.card φ.ker ∣ Nat.card (pPrimeCore 2 ↥M) := by
      rw [← Subgroup.card_map_of_injective C.subtype_injective]
      exact Subgroup.card_dvd_of_le hle
    intro h2
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (h2.trans hc))
  obtain ⟨hbij, -, hequiv⟩ :=
    CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection φ hφs hφk
  have hCX : C.map M.subtype = centralizer {m} ⊓ centralizer {b} := by
    rw [map_subtype_centralizer hbm, inf_comm]
  let eC : ↥C ≃* ↥(centralizer ({m} : Set X) ⊓ centralizer {b}) :=
    (C.equivMapOfInjective M.subtype M.subtype_injective).trans (MulEquiv.subgroupCongr hCX)
  have hĴ : IsPComponent 2 ((J.subgroupOf (centralizer {m} ⊓ centralizer {b})).map
      eC.symm.toMonoidHom) :=
    isPComponent_map_mulEquiv eC.symm ((isTwoComponentIn_iff hJ.1).mp hJ)
  have h1 := hbij.mapsTo hĴ
  have hJb : ∀ x ∈ J, x * b = b * x := fun x hx =>
    mem_centralizer_singleton_iff.mp (mem_inf.mp (hJ.1 hx)).2
  have hle : barOf (centralizer {m}) J ≤ centralizer {(QuotientGroup.mk ⟨b, hbm⟩ : MBar m)} := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_centralizer_singleton_iff]
    change π x * π b' = π b' * π x
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hJb _ hx)
  refine ⟨hle, ?_⟩
  have hid : ((J.subgroupOf (centralizer {m} ⊓ centralizer {b})).map eC.symm.toMonoidHom).map
      φ = (barOf (centralizer {m}) J).subgroupOf
        (centralizer {(QuotientGroup.mk ⟨b, hbm⟩ : MBar m)}) := by
    ext ⟨y, hy⟩
    constructor
    · rintro ⟨c, hc, hcy⟩
      rw [SetLike.mem_coe, Subgroup.mem_map_equiv, MulEquiv.symm_symm] at hc
      refine ⟨(c : ↥M), hc, ?_⟩
      exact congrArg Subtype.val hcy
    · rintro ⟨x, hx, hxy⟩
      have hxC : x ∈ C := by
        rw [mem_centralizer_singleton_iff]
        exact Subtype.ext (hJb _ hx)
      refine ⟨⟨x, hxC⟩, ?_, Subtype.ext hxy⟩
      rw [SetLike.mem_coe, Subgroup.mem_map_equiv, MulEquiv.symm_symm]
      exact hx
  refine ⟨hid ▸ h1, ?_⟩
  obtain ⟨e, -⟩ := hequiv _ hĴ
  let e1 : ↥J ≃* ↥((J.subgroupOf (centralizer {m} ⊓ centralizer {b})).map
      eC.symm.toMonoidHom) :=
    (subgroupOfEquivOfLe hJ.1).symm.trans (Subgroup.equivMapOfInjective _ _ eC.symm.injective)
  let e2 : ↥(((J.subgroupOf (centralizer {m} ⊓ centralizer {b})).map
      eC.symm.toMonoidHom).map φ) ≃* ↥(barOf (centralizer {m}) J) :=
    (MulEquiv.subgroupCongr hid).trans (subgroupOfEquivOfLe hle)
  exact ⟨(UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 e1).trans
    (e.trans (UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 e2))⟩

theorem barOf_le_layer {X : Type} [Group X] [Finite X] {m b : X}
    (hbm : b ∈ centralizer ({m} : Set X)) (hb : orderOf b = 2)
    (hSchF : LBalance.SchreierSections (MBar m)) {J : Subgroup X}
    (hJ : IsTwoComponentIn J (centralizer {m} ⊓ centralizer {b})) :
    barOf (centralizer {m}) J ≤ layer (MBar m) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hle, hpc, -⟩ := isPComponent_barOf hbm hb hJ
  have hb2 : ∃ n : ℕ, (QuotientGroup.mk ⟨b, hbm⟩ : MBar m) ^ 2 ^ n = 1 := by
    refine ⟨1, ?_⟩
    rw [pow_one, ← QuotientGroup.mk_pow]
    have h1 : (⟨b, hbm⟩ : ↥(centralizer ({m} : Set X))) ^ 2 = 1 := Subtype.ext (by
      change b ^ 2 = 1
      rw [← hb, pow_orderOf_eq_one])
    rw [h1, QuotientGroup.mk_one]
  have hbal := LBalance.pLayer_centralizer_element_le hSchF hb2
  rw [ClassicalInvolution.LBalanceProof.pLayer_eq_layer_of_pPrimeCore_eq_bot
    (pPrimeCore_quotient_pPrimeCore_eq_bot 2)] at hbal
  intro y hy
  have hy' : (⟨y, hle hy⟩ : ↥(centralizer {(QuotientGroup.mk ⟨b, hbm⟩ : MBar m)})) ∈
      (barOf (centralizer {m}) J).subgroupOf
        (centralizer {(QuotientGroup.mk ⟨b, hbm⟩ : MBar m)}) := hy
  exact hbal ⟨_, (le_sSup (s := {L : Subgroup ↥(centralizer
    {(QuotientGroup.mk ⟨b, hbm⟩ : MBar m)}) | IsPComponent 2 L}) hpc :
      _ ≤ pLayer ↥(centralizer {(QuotientGroup.mk ⟨b, hbm⟩ : MBar m)}) 2) hy', rfl⟩

end L415

variable {X : Type} [Group X] [Finite X]
  {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X} {w z : X} {V : Subgroup X}
  {i j : ℕ} {z₁ τ α : X} {K₂ W 𝒱 : Subgroup X}

namespace Data415B

variable (hD : Data415B t L p f S w z V i j z₁ τ α K₂ W 𝒱)
include hD

theorem beta_mem_F : w ^ (orderOf w / 2) * t ^ i * z ^ j ∈ centralizer ({z₁} : Set X) :=
  mem_centralizer_singleton_iff.mpr hD.beta_comm_z₁

theorem orderOf_beta : orderOf (w ^ (orderOf w / 2) * t ^ i * z ^ j) = 2 :=
  orderOf_eq_prime (by rw [sq]; exact hD.beta_mul_beta) hD.hs.beta.ne_one

theorem centralizer_z₁_ne_top [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a) :
    centralizer ({z₁} : Set X) ≠ ⊤ := by
  intro htop
  have hcen : center X = ⊥ := by
    rcases (inferInstance : (center X).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      exact hab ((mem_center_iff.mp (show a ∈ center X by rw [ht]; exact mem_top a) b).symm)
  apply hD.z₁_ne_one
  have hmem : z₁ ∈ center X := by
    rw [mem_center_iff]
    intro g
    have : g ∈ centralizer ({z₁} : Set X) := by
      rw [htop]
      exact mem_top g
    exact mem_centralizer_singleton_iff.mp this
  rwa [hcen, mem_bot] at hmem

theorem schreierSections_F [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X)
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog) :
    LBalance.SchreierSections (MBar z₁) := by
  have hKF := UnbalancedCorr.isKGroupCat_of_ne_top hK (hD.centralizer_z₁_ne_top hnab)
  have hKFbar : SectionRank.IsKGroupCat (MBar z₁) :=
    GSThmB.OddQuot.isKGroupCat_of_surjective hKF _ (QuotientGroup.mk'_surjective _)
  exact GSThmB.schreierSections_of_isKGroupCat hSch hKFbar

theorem barOf_K₂_le_layer [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X)
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog) :
    barOf (centralizer {z₁}) K₂ ≤ layer (MBar z₁) :=
  L415.barOf_le_layer hD.beta_mem_F hD.orderOf_beta (hD.schreierSections_F hnab hK hSch)
    hD.fd.isTwoComponentIn_K₂

theorem orderOf_betaBar :
    orderOf (QuotientGroup.mk ⟨w ^ (orderOf w / 2) * t ^ i * z ^ j, hD.beta_mem_F⟩ :
      MBar z₁) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card (pPrimeCore 2 ↥(centralizer ({z₁} : Set X)))) :=
    Nat.coprime_two_left.mp pPrimeCore_coprime_card
  exact orderOf_mk_eq_two hodd (by rw [Subgroup.orderOf_mk]; exact hD.orderOf_beta)

theorem exists_orbit_component [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X)
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog) :
    ∃ M : Subgroup (MBar z₁), IsPComponent 2 M ∧
      barOf (centralizer {z₁}) K₂ ≤ M ⊔ conjugate M
        (QuotientGroup.mk ⟨w ^ (orderOf w / 2) * t ^ i * z ^ j, hD.beta_mem_F⟩) ∧
      IsPComponent 2 ((barOf (centralizer {z₁}) K₂).subgroupOf
        ((M ⊔ conjugate M (QuotientGroup.mk ⟨w ^ (orderOf w / 2) * t ^ i * z ^ j,
          hD.beta_mem_F⟩)) ⊓ centralizer {(QuotientGroup.mk
            ⟨w ^ (orderOf w / 2) * t ^ i * z ^ j, hD.beta_mem_F⟩ : MBar z₁)})) := by
  obtain ⟨hle, hpc, -⟩ := L415.isPComponent_barOf hD.beta_mem_F hD.orderOf_beta
    hD.fd.isTwoComponentIn_K₂
  have hE := hD.barOf_K₂_le_layer hnab hK hSch
  rw [← ClassicalInvolution.LBalanceProof.pLayer_eq_layer_of_pPrimeCore_eq_bot
    (pPrimeCore_quotient_pPrimeCore_eq_bot 2)] at hE
  exact two_layer_fixed_component_orbit_location hD.orderOf_betaBar hle hpc hE

end Data415B

end CFSG.ComponentClassification.HarrisLit
