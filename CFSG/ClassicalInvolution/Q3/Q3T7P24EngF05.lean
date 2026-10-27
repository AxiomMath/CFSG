module

public import CFSG.ClassicalInvolution.Q3.Q3T7P24EngF04
public import CFSG.ClassicalInvolution.Asc77.AscS24BDec
import CFSG.ClassicalInvolution.Q3.Q3T7P24EngB
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

namespace Asc77
namespace S24B
namespace Ctx8Frame

section
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Disconnected.AschTight (HypOmegaGen)
open CFSG.ClassicalInvolution.Asc77.S24B
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_rep_of_le {W : Subgroup G} (c : Q3CL.Thompson.Ctx Ω W) {S₀ : Sylow 2 G}
    (hWS₀ : W ≤ (S₀ : Subgroup G)) {J T : Subgroup G} (hJ : J ∈ Ω) (hT : T ∈ RSet Ω)
    (hTJ : T ≤ J) (hTS : T ≤ (S₀ : Subgroup G)) :
    ∃ ρ : Thompson.Rep Ω W, ρ.K = J ∧ ρ.R = T := by
  have hTD : T ∈ DSet Ω W := Q3CL.Thompson.mem_DSet_of_le_sylow c.hΩ c.hW hWS₀ hT hTS
  have hTsyl : IsSylow2In T J := T7C.isSylow2In_of_mem_RSet_of_le c.hΩ hJ hT hTJ
  have hcard := Q3CL.Thompson.D_card c.hΩ c.hW hTD
  have hpos : 0 < Nat.card ↥T := Nat.card_pos
  have hnot : ¬ T ≤ W := by
    intro hle
    have : T ⊓ W = T := inf_eq_left.mpr hle
    rw [this] at hcard
    omega
  obtain ⟨r, hrT, hrW⟩ := Set.not_subset.mp hnot
  exact ⟨⟨J, T, r, hJ, hTD, hTsyl, hrT, hrW⟩, rfl, rfl⟩

end

section
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Disconnected.AschTight (HypOmegaGen)
open CFSG.ClassicalInvolution.Asc77.S24B
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
open CFSG.ClassicalInvolution.Asc77.S24B.Ctx8
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Asc77.S24B.Ctx8Frame Ω K K' W S R R' z u)

include C in
theorem card_K_inf_W : Nat.card ↥(K ⊓ W) = 4 := by
  have h := (Q3CL.Thompson.inf_W_of_mem_D C.D.c.hΩ C.D.c.hW C.D.F.ρ.hR
    C.D.F.ρ.hK C.D.F.ρ.hRK).1
  rw [C.hK] at h
  rw [← h, ← C.D.h₁, Nat.card_zpowers, C.orderOf_x₁]

theorem card_J_inf_W : Nat.card ↥(C.D.F.ρ₃.K ⊓ W) = 4 := by
  have h := (Q3CL.Thompson.inf_W_of_mem_D C.D.c.hΩ C.D.c.hW C.D.F.ρ₃.hR
    C.D.F.ρ₃.hK C.D.F.ρ₃.hRK).1
  rw [← h, ← C.D.h₃, Nat.card_zpowers, C.orderOf_x₃]

include C in
theorem not_alt_two {S₀ : Sylow 2 G} (hWS₀ : W ≤ (S₀ : Subgroup G))
    (h2 : ∀ L ∈ Ω, 2 < Nat.card ↥(L ⊓ (S₀ : Subgroup G)) → L ⊓ (S₀ : Subgroup G) ∈ RSet Ω) :
    False := by
  set J := C.D.F.ρ₃.K with hJdef
  have hKS : 2 < Nat.card ↥(K ⊓ (S₀ : Subgroup G)) :=
    lt_of_lt_of_le (by rw [C.card_K_inf_W]; norm_num)
      (Subgroup.card_le_of_le (inf_le_inf_left K hWS₀))
  have hJS : 2 < Nat.card ↥(J ⊓ (S₀ : Subgroup G)) :=
    lt_of_lt_of_le (by rw [C.card_J_inf_W]; norm_num)
      (Subgroup.card_le_of_le (inf_le_inf_left J hWS₀))
  have hK1 := h2 K C.mem hKS
  have hJ1 := h2 J C.D.F.ρ₃.hK hJS
  obtain ⟨ρa, hρaK, hρaR⟩ := exists_rep_of_le C.D.c hWS₀ C.mem hK1 inf_le_left inf_le_right
  obtain ⟨ρb, hρbK, hρbR⟩ :=
    exists_rep_of_le C.D.c hWS₀ C.D.F.ρ₃.hK hJ1 inf_le_left inf_le_right
  have hne : K ⊓ (S₀ : Subgroup G) ≠ J ⊓ (S₀ : Subgroup G) := by
    intro h
    have hle : K ⊓ (S₀ : Subgroup G) ≤ J := h ▸ inf_le_left
    have h4 : 4 ≤ Nat.card ↥(K ⊓ (S₀ : Subgroup G)) := by
      have := Subgroup.card_le_of_le (inf_le_inf_left K hWS₀)
      rw [C.card_K_inf_W] at this
      exact this
    exact C.D.F.hne₁ (C.hK.trans (C.hyp.eq_of_le_of_le C.mem C.D.F.ρ₃.hK
      (S₀.isPGroup'.to_inf_right) h4 inf_le_left hle))
  have hcomm := l6_7_proved G Ω C.hyp S₀ _ hK1 _ hJ1 inf_le_right
    inf_le_right hne
  have hab : ρa.r * ρb.r = ρb.r * ρa.r :=
    hcomm _ (hρaR ▸ ρa.hr) _ (hρbR ▸ ρb.hr)
  have hia : ρa.img = C.D.F.ρ.img := C.D.c.img_eq_of_K_eq ρa C.D.F.ρ (hρaK.trans C.hK.symm)
  have hib : ρb.img = C.D.F.ρ₃.img := C.D.c.img_eq_of_K_eq ρb C.D.F.ρ₃ hρbK
  apply C.D.hac
  apply Subtype.ext
  change C.D.F.ρ.img * C.D.F.ρ₃.img = C.D.F.ρ₃.img * C.D.F.ρ.img
  rw [← hia, ← hib]
  unfold Thompson.Rep.img
  rw [← Thompson.piG_mul ρa.r_mem_normalizer ρb.r_mem_normalizer,
    ← Thompson.piG_mul ρb.r_mem_normalizer ρa.r_mem_normalizer, hab]

include C in
theorem le_normalizer_W : (S : Subgroup G) ≤ Subgroup.normalizer (W : Set G) := by
  obtain ⟨η, hηG, hWη⟩ := id C.hd.hW
  obtain ⟨S₀, hηS₀, hinv⟩ := id hηG
  have hUS₀ : ∀ U ∈ η, U ≤ (S₀ : Subgroup G) := fun U hU => (hηS₀.1 hU).2
  have hWS₀ : W ≤ (S₀ : Subgroup G) := by
    rw [hWη]; exact iSup₂_le fun U hU => hUS₀ U hU
  have hP : PartIHyp Ω := ⟨C.hyp, C.partI.cls, C.partI.aEmpty⟩
  have htr : ∀ K₁ ∈ Ω, ∀ J ∈ Ω, ∃ g : G, conjSub g K₁ = J := by
    intro K₁ hK₁ J hJ
    obtain ⟨g₁, rfl⟩ := C.trans K₁ hK₁
    obtain ⟨g₂, rfl⟩ := C.trans J hJ
    exact ⟨g₂ * g₁⁻¹, by rw [conjSub_mul, conjSub_inv_conjSub]⟩
  have h612 := Disconnected.AschTight.Sec7.l6_12_mod G Ω hP htr S₀
  dsimp only at h612
  rcases h612 with ⟨η₀, -, -, huniq, hwc⟩ | h2
  · have hMS₀ : (⨆ U ∈ {U : Subgroup G | (∃ η ∈ etaG Ω, U ∈ η) ∧ U ≤ (S₀ : Subgroup G)}, U) ≤
        (S₀ : Subgroup G) := iSup₂_le fun U hU => hU.2
    have hηeq : η = η₀ := huniq η hηG fun m hm U hU => hinv m (hMS₀ hm) U hU
    subst hηeq
    intro s hs
    obtain ⟨x, hx⟩ := exists_conjSub_eq_of_sylow S₀ S
    have hU_S : ∀ U ∈ η, U ≤ (S : Subgroup G) := fun U hU =>
      (hWη ▸ le_iSup₂ (f := fun V (_ : V ∈ η) => V) U hU : U ≤ W).trans C.hd.hWS
    have hback : ∀ {A : Subgroup G}, A ≤ (S : Subgroup G) →
        conjSub x⁻¹ A ≤ (S₀ : Subgroup G) := fun {A} hA => by
      rw [conjSub_le_iff, inv_inv, hx]; exact hA
    have h1 : ∀ U ∈ η, conjSub (x⁻¹ * s) U ∈ η := by
      refine hwc (x⁻¹ * s) fun U hU => ?_
      rw [conjSub_mul]
      refine hback ?_
      have h := conjSub_mono (n := s) (hU_S U hU)
      rwa [conjSub_eq_self_of_mem hs] at h
    have h2 : ∀ U ∈ η, conjSub x⁻¹ U ∈ η := hwc x⁻¹ fun U hU => hback (hU_S U hU)
    have e1 : conjSub (x⁻¹ * s) W = W := by
      rw [hWη]; exact AschTight.Sec7.conjSub_iSup_eq_of_forall_mem h1
    have e2 : conjSub x⁻¹ W = W := by
      rw [hWη]; exact AschTight.Sec7.conjSub_iSup_eq_of_forall_mem h2
    have e3 : conjSub x W = W := by
      conv_lhs => rw [← e2]
      exact conjSub_conjSub_inv x W
    refine mem_normalizer_iff_conjSub_eq.mpr ?_
    calc conjSub s W = conjSub (x * (x⁻¹ * s)) W := by group
      _ = W := by rw [conjSub_mul, e1, e3]
  · exact (C.not_alt_two hWS₀ h2).elim

include C in
theorem hRsyl : IsSylow2In R K :=
  T7C.isSylow2In_of_mem_RSet_of_le C.hyp C.mem C.hd.hR.1
    C.hd.hR.2.1

include C in
theorem z_mem_R : z ∈ R :=
  T7C.mem_of_isSylow2In C.hyp C.mem C.hRsyl C.hzK

include C in
theorem conjSub_K_mem {y : G} (hy : y ∈ (S : Subgroup G)) :
    conjSub y K = K ∨ conjSub y K = K' := by
  have hΩ := C.hyp
  have hT : conjSub y R ∈ RSet Ω := RSet.conj hΩ.conjInvariant C.hd.hR.1 y
  have hTS : conjSub y R ≤ (S : Subgroup G) := by
    have h := conjSub_mono (n := y) C.hd.hR.2.2
    rwa [conjSub_eq_self_of_mem hy] at h
  have hL : conjSub y K ∈ Ω := hΩ.conjInvariant y K C.mem
  have hTL : conjSub y R ≤ conjSub y K := conjSub_mono C.hd.hR.2.1
  have hT2 : IsPGroup 2 ↥(conjSub y R) := S.isPGroup'.to_le hTS
  have h8 : Nat.card ↥(conjSub y R) = 8 := by
    rw [← C.h8]
    exact Nat.card_congr (Subgroup.equivMapOfInjective R (MulAut.conj y).toMonoidHom
      (MulAut.conj y).injective).symm.toEquiv
  by_cases hTR : conjSub y R = R
  · left
    exact (hΩ.eq_of_le_of_le C.mem hL hT2 (by omega) ((le_of_eq hTR).trans C.hd.hR.2.1)
      hTL).symm
  · by_cases hLK : conjSub y K = K
    · exact Or.inl hLK
    · right
      have hcomm := l6_7_proved G Ω hΩ S R C.hd.hR.1 _ hT C.hd.hR.2.2 hTS
        (Ne.symm hTR)
      have hTc : conjSub y R ≤ Subgroup.centralizer ({z} : Set G) := fun t ht => by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hcomm z C.z_mem_R t ht).symm
      have hTN := hΩ.le_normalizer_of_le_centralizer C.mem hL (Ne.symm hLK)
        C.hzK hTL hT2 (by omega) hTc
      have hnbr : conjSub y K ∈ omegaNbr Ω K := ⟨hL, hLK, _, hT, hTL, hTN⟩
      have hperp : conjSub y K ∈ KPerp Ω K := Set.mem_insert_of_mem _ hnbr
      rw [C.perp] at hperp
      rcases hperp with h | h
      · exact absurd h hLK
      · exact h

include C in
theorem img_conj_eq_of_fix {y : G} (hy : y ∈ Subgroup.normalizer (W : Set G))
    (ρ : Thompson.Rep Ω W) (h : conjSub y ρ.K = ρ.K) :
    Thompson.piG W y * ρ.img * (Thompson.piG W y)⁻¹ = ρ.img := by
  rw [← T7D.conjRep_img C.D.c.hΩ hy ρ]
  exact C.D.c.img_eq_of_K_eq _ ρ h

theorem φ_imgQ_mem (ρ : Thompson.Rep Ω W) : C.D.φ (T7D.imgQ ρ) ∈ S4.swaps4 :=
  S4.mem_swaps4_of_isSwap ((C.D.hφ _).mp (T7D.imgQ_mem ρ))

theorem closure_frame_eq_top :
    Subgroup.closure ({T7D.imgQ C.D.F.ρ, T7D.imgQ C.D.F.ρ', T7D.imgQ C.D.F.ρ₃} :
      Set ↥(muGroup Ω W)) = ⊤ := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.closure_frame_eq_top_of C.D.F C.D.φ C.D.hφ C.D.hab C.D.hcomm
    C.D.hac

theorem trivMu_of_fix {y : G} (hy : y ∈ Subgroup.normalizer (W : Set G))
    (h₁ : conjSub y C.D.F.ρ.K = C.D.F.ρ.K) (h₂ : conjSub y C.D.F.ρ'.K = C.D.F.ρ'.K)
    (h₃ : conjSub y C.D.F.ρ₃.K = C.D.F.ρ₃.K) : TrivMu Ω W y := by
  set q := Thompson.piG W y
  let Z : Subgroup ↥(muGroup Ω W) :=
    (Subgroup.centralizer ({q} : Set (NQuot (W ⊔ OCW W)))).comap (muGroup Ω W).subtype
  have hmem : ∀ ρ : Thompson.Rep Ω W, conjSub y ρ.K = ρ.K → T7D.imgQ ρ ∈ Z := by
    intro ρ hρ
    show (T7D.imgQ ρ : NQuot (W ⊔ OCW W)) ∈ Subgroup.centralizer ({q} : Set (NQuot (W ⊔ OCW W)))
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := C.img_conj_eq_of_fix hy ρ hρ
    change q * ρ.img * q⁻¹ = ρ.img at h
    change ρ.img * q = q * ρ.img
    calc ρ.img * q = q * ρ.img * q⁻¹ * q := by rw [h]
      _ = q * ρ.img := by group
  have hZ : Z = ⊤ := by
    rw [eq_top_iff, ← C.closure_frame_eq_top, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact hmem _ h₁
    · exact hmem _ h₂
    · exact hmem _ h₃
  intro m hm
  have hmN : m ∈ Subgroup.normalizer (W : Set G) := Thompson.MGrp_le_normalizer Ω W hm
  have hmμ : Thompson.piG W m ∈ muGroup Ω W :=
    Thompson.piG_mem_muGroup (Subgroup.mem_sup_left hm)
  have hc : (⟨Thompson.piG W m, hmμ⟩ : ↥(muGroup Ω W)) ∈ Z := hZ ▸ Subgroup.mem_top _
  have hc' : Thompson.piG W m * q = q * Thompson.piG W m :=
    Subgroup.mem_centralizer_singleton_iff.mp hc
  have hx : y * m * y⁻¹ * m⁻¹ ∈ Subgroup.normalizer (W : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hy hmN) (Subgroup.inv_mem _ hy))
      (Subgroup.inv_mem _ hmN)
  rw [← Thompson.piG_eq_one_iff hx, Thompson.piG_mul (Subgroup.mul_mem _
      (Subgroup.mul_mem _ hy hmN) (Subgroup.inv_mem _ hy)) (Subgroup.inv_mem _ hmN),
    Thompson.piG_mul (Subgroup.mul_mem _ hy hmN) (Subgroup.inv_mem _ hy),
    Thompson.piG_mul hy hmN, Thompson.piG_inv hy, Thompson.piG_inv hmN]
  change q * Thompson.piG W m * q⁻¹ * (Thompson.piG W m)⁻¹ = 1
  rw [← hc']
  group

end

section
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Disconnected.AschTight (HypOmegaGen)
open scoped Pointwise
open CFSG.ClassicalInvolution.Asc77.S24B
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem le_normalizer_MGrp [Finite G] (hΩ : HypOmegaMod Ω) {W : Subgroup G} :
    Subgroup.normalizer (W : Set G) ≤ Subgroup.normalizer (MGrp Ω W : Set G) := by
  have key : ∀ n ∈ Subgroup.normalizer (W : Set G), conjSub n (MGrp Ω W) ≤ MGrp Ω W := by
    intro n hn
    rw [conjSub_le_iff]
    refine iSup₂_le fun R hR => ?_
    rw [← conjSub_le_iff]
    exact Thompson.le_MGrp_of_mem_D (Q3CL.Thompson.conjSub_mem_D hΩ hR hn)
  intro n hn
  refine mem_normalizer_iff_conjSub_eq.mpr (le_antisymm (key n hn) ?_)
  have h := conjSub_mono (n := n) (key n⁻¹ (Subgroup.inv_mem _ hn))
  rwa [conjSub_conjSub_inv] at h

end

section
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Disconnected.AschTight (HypOmegaGen)
open scoped Pointwise
open CFSG.ClassicalInvolution.Asc77.S24B
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
open CFSG.ClassicalInvolution.Asc77.S24B.Ctx8
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Asc77.S24B.Ctx8Frame Ω K K' W S R R' z u)

include C in
theorem isSylow2In_P : IsSylow2In ((S : Subgroup G) ⊓ MGrp Ω W) (MGrp Ω W) :=
  AschTight.Hall196.isSylow2In_inf_of_le_normalizer S
    (C.le_normalizer_W.trans (le_normalizer_MGrp C.hyp))

include C in
theorem exists_swap : ∃ x ∈ (S : Subgroup G) ⊓ MGrp Ω W, conjSub x K = K' := by
  have hP := C.isSylow2In_P
  let PS : Sylow 2 ↥(MGrp Ω W) := AscQuot.sylowOfIsSylow2In' hP
  let PB : Sylow 2 ↥(muGroup Ω W) := PS.mapSurjective (piM_surjective W)
  have hmemPB : ∀ q, q ∈ (PB : Subgroup ↥(muGroup Ω W)) ↔
      ∃ x : ↥(MGrp Ω W), (x : G) ∈ (S : Subgroup G) ∧ piM Ω W x = q := by
    intro q
    change q ∈ (PS : Subgroup ↥(MGrp Ω W)).map (piM Ω W) ↔ _
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, (Subgroup.mem_subgroupOf.mp hx).1, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, Subgroup.mem_subgroupOf.mpr ⟨hx, x.2⟩, rfl⟩
  have hcardμ : Nat.card ↥(muGroup Ω W) = 24 := by
    rw [Nat.card_congr C.D.φ.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm,
      Fintype.card_fin]
    rfl
  have h8 : 2 ^ 3 ∣ Nat.card ↥(PB : Subgroup ↥(muGroup Ω W)) :=
    Sylow.pow_dvd_card_of_pow_dvd_card PB (by rw [hcardμ]; norm_num)
  set ra := T7D.imgQ C.D.F.ρ with hra
  set ta := T7D.imgQ C.D.F.ρ' with hta
  have hrM : C.D.F.ρ.r ∈ MGrp Ω W := Thompson.le_MGrp_of_mem_D C.D.F.ρ.hR C.D.F.ρ.hr
  have hraP : ra ∈ (PB : Subgroup ↥(muGroup Ω W)) :=
    (hmemPB ra).mpr ⟨⟨_, hrM⟩, C.hd.hR.2.2 C.r_mem_R, rfl⟩
  have hab : C.D.φ ra ≠ C.D.φ ta := fun h => C.D.hab (C.D.φ.injective h)
  have hcomm : C.D.φ ra * C.D.φ ta = C.D.φ ta * C.D.φ ra := by
    rw [← map_mul, ← map_mul, C.D.hcomm]
  have hsw_r := C.φ_imgQ_mem C.D.F.ρ
  have hsw_t := C.φ_imgQ_mem C.D.F.ρ'
  obtain ⟨h, hhP, hh⟩ : ∃ h ∈ (PB : Subgroup ↥(muGroup Ω W)),
      ¬ (h = 1 ∨ h = ra ∨ h = ta ∨ h = ra * ta) := by
    by_contra hcon
    push Not at hcon
    have hsub : ((PB : Subgroup ↥(muGroup Ω W)) : Set ↥(muGroup Ω W)) ⊆
        {1, ra, ta, ra * ta} := by
      intro x hx
      rcases hcon x hx with h | h | h | h <;> simp [h]
    have hle : Nat.card ↥(PB : Subgroup ↥(muGroup Ω W)) ≤ 4 := by
      rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
      refine (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ?_
      refine (Set.ncard_insert_le _ _).trans ?_
      refine (Nat.add_le_add_right (Set.ncard_insert_le _ _) 1).trans ?_
      refine (Nat.add_le_add_right (Nat.add_le_add_right (Set.ncard_insert_le _ _) 1) 1).trans ?_
      rw [Set.ncard_singleton]
    have hpos : 0 < Nat.card ↥(PB : Subgroup ↥(muGroup Ω W)) := Nat.card_pos
    obtain ⟨k, hk⟩ := h8
    omega
  have hnc : h * ra ≠ ra * h := by
    intro hc
    have hc' : C.D.φ h * C.D.φ ra = C.D.φ ra * C.D.φ h := by rw [← map_mul, ← map_mul, hc]
    rcases perm4_cent_swap (C.D.φ h) _ hsw_r _ hsw_t hab hcomm hc' with e | e | e | e
    · exact hh (Or.inl (C.D.φ.injective (e.trans (map_one C.D.φ).symm)))
    · exact hh (Or.inr (Or.inl (C.D.φ.injective e)))
    · exact hh (Or.inr (Or.inr (Or.inl (C.D.φ.injective e))))
    · exact hh (Or.inr (Or.inr (Or.inr (C.D.φ.injective (e.trans (map_mul C.D.φ ra ta).symm)))))
  have hcP : h * ra * h⁻¹ ∈ (PB : Subgroup ↥(muGroup Ω W)) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hhP hraP) (Subgroup.inv_mem _ hhP)
  have hcsw : C.D.φ (h * ra * h⁻¹) ∈ S4.swaps4 := by
    rw [map_mul, map_mul, map_inv]
    exact perm4_conj_swap _ _ hsw_r
  have hcab : h * ra * h⁻¹ = ta := by
    by_contra hne
    have hne' : C.D.φ (h * ra * h⁻¹) ≠ C.D.φ ta := fun e => hne (C.D.φ.injective e)
    have hne'' : C.D.φ (h * ra * h⁻¹) ≠ C.D.φ ra := by
      intro e
      apply hnc
      have e' := C.D.φ.injective e
      calc h * ra = h * ra * h⁻¹ * h := by group
        _ = ra * h := by rw [e']
    obtain ⟨h3, h1⟩ := perm4_mul_swap_cube _ hsw_r _ hsw_t hab hcomm _ hcsw hne'' hne'
    have hy : ra * (h * ra * h⁻¹) ∈ (PB : Subgroup ↥(muGroup Ω W)) := Subgroup.mul_mem _ hraP hcP
    have hy3 : (ra * (h * ra * h⁻¹)) ^ 3 = 1 := by
      apply C.D.φ.injective
      rw [map_pow, map_mul, h3, map_one]
    apply h1
    rw [← map_mul, eq_one_of_pow_three PB.isPGroup' hy hy3, map_one]
  obtain ⟨x, hxS, hx⟩ := (hmemPB h).mp hhP
  have hxN : (x : G) ∈ Subgroup.normalizer (W : Set G) := Thompson.MGrp_le_normalizer Ω W x.2
  refine ⟨x, ⟨hxS, x.2⟩, ?_⟩
  have himg : (T7D.conjRep C.D.c.hΩ hxN C.D.F.ρ).img = C.D.F.ρ'.img := by
    rw [T7D.conjRep_img]
    have e := congrArg Subtype.val hcab
    have hxv : Thompson.piG W (x : G) = (h : NQuot (W ⊔ OCW W)) := by
      rw [← hx]; rfl
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at e
    rw [hxv]
    exact e
  have hKK := C.D.c.K_eq_of_img_eq _ _ himg
  change conjSub (x : G) C.D.F.ρ.K = C.D.F.ρ'.K at hKK
  exact (congrArg (conjSub (x : G)) C.hK).symm.trans (hKK.trans C.hK')

end

section
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Disconnected.AschTight (HypOmegaGen)
open CFSG.ClassicalInvolution.Asc77.S24B
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
open CFSG.ClassicalInvolution.Asc77.S24B.Ctx8
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Asc77.S24B.Ctx8Frame Ω K K' W S R R' z u)

include C in
theorem conjSub_K'_of_K {y : G} (h : conjSub y K = K) : conjSub y K' = K' := by
  have h1 := twinSet_conj C.hyp.conjInvariant C.hK'tw y
  rw [h, C.twinSet_eq] at h1
  rcases h1 with h1 | h1
  · exact absurd ((conjSub_inj y).mp (h1.trans h.symm)) C.hne
  · exact h1

include C in
theorem mem_normalizer_K'_of_mem_K {x : G} (hx : x ∈ K) :
    x ∈ Subgroup.normalizer (K' : Set G) :=
  C.hyp.le_normalizer_of_twin C.mem C.hK'tw.1 C.hne.symm C.hzK C.hzK' hx

include C in
theorem mem_normalizer_K_of_mem_K' {x : G} (hx : x ∈ K') :
    x ∈ Subgroup.normalizer (K : Set G) :=
  C.hyp.le_normalizer_of_twin C.hK'tw.1 C.mem C.hne C.hzK' C.hzK hx

theorem piG_r_sq : Thompson.piG W C.D.F.ρ.r * Thompson.piG W C.D.F.ρ.r = 1 := by
  rw [← Thompson.piG_mul C.D.F.ρ.r_mem_normalizer C.D.F.ρ.r_mem_normalizer, C.r_mul_self]
  exact Thompson.piG_of_mem_sup (Subgroup.mem_sup_left C.hd.hzW)

theorem piG_t_sq : Thompson.piG W C.D.F.ρ'.r * Thompson.piG W C.D.F.ρ'.r = 1 := by
  rw [← Thompson.piG_mul C.D.F.ρ'.r_mem_normalizer C.D.F.ρ'.r_mem_normalizer, C.t_mul_self]
  exact Thompson.piG_of_mem_sup (Subgroup.mem_sup_left C.hd.hzW)

theorem fix_J_of {y w : G} (hy : y ∈ Subgroup.normalizer (W : Set G))
    (hw : w ∈ Subgroup.normalizer (W : Set G))
    (h : Thompson.piG W y * C.D.F.ρ₃.img * (Thompson.piG W y)⁻¹ =
      Thompson.piG W w * C.D.F.ρ₃.img * (Thompson.piG W w)⁻¹) :
    conjSub (w⁻¹ * y) C.D.F.ρ₃.K = C.D.F.ρ₃.K := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.fix_J_of_of C.D.c C.D.F.ρ₃ hy hw h

theorem good_r : C.D.F.ρ.r ∈ (S : Subgroup G) ⊓ MGrp Ω W ∧ conjSub C.D.F.ρ.r K = K ∧
    conjSub C.D.F.ρ.r K' = K' :=
  ⟨⟨C.hd.hR.2.2 C.r_mem_R, Thompson.le_MGrp_of_mem_D C.D.F.ρ.hR C.D.F.ρ.hr⟩,
    conjSub_eq_self_of_mem C.r_mem_K,
    mem_normalizer_iff_conjSub_eq.mp (C.mem_normalizer_K'_of_mem_K C.r_mem_K)⟩

theorem good_t : C.D.F.ρ'.r ∈ (S : Subgroup G) ⊓ MGrp Ω W ∧ conjSub C.D.F.ρ'.r K = K ∧
    conjSub C.D.F.ρ'.r K' = K' :=
  ⟨⟨C.hd.hR'.2.2 C.t_mem_R', Thompson.le_MGrp_of_mem_D C.D.F.ρ'.hR C.D.F.ρ'.hr⟩,
    mem_normalizer_iff_conjSub_eq.mp (C.mem_normalizer_K_of_mem_K' C.t_mem_K'),
    conjSub_eq_self_of_mem C.t_mem_K'⟩

theorem exists_fix_J {y : G} (hy : y ∈ (S : Subgroup G)) (hK : conjSub y K = K)
    (hK' : conjSub y K' = K') :
    ∃ w : G, (w ∈ (S : Subgroup G) ⊓ MGrp Ω W ∧ conjSub w K = K ∧ conjSub w K' = K') ∧
      conjSub (w⁻¹ * y) C.D.F.ρ₃.K = C.D.F.ρ₃.K := by
  have hyN : y ∈ Subgroup.normalizer (W : Set G) := C.le_normalizer_W hy
  set q := Thompson.piG W y with hq
  have hr : q * C.D.F.ρ.img * q⁻¹ = C.D.F.ρ.img :=
    C.img_conj_eq_of_fix hyN C.D.F.ρ (by rw [C.hK]; exact hK)
  have ht : q * C.D.F.ρ'.img * q⁻¹ = C.D.F.ρ'.img :=
    C.img_conj_eq_of_fix hyN C.D.F.ρ' (by rw [C.hK']; exact hK')
  set σ := T7D.conjRep C.D.c.hΩ hyN C.D.F.ρ₃ with hσdef
  have hσ : σ.img = q * C.D.F.ρ₃.img * q⁻¹ := T7D.conjRep_img _ _ _
  have hrs : C.D.F.ρ.img * C.D.F.ρ₃.img ≠ C.D.F.ρ₃.img * C.D.F.ρ.img :=
    fun h => C.D.hac ((imgQ_comm_iff _ _).mpr h)
  have hts : C.D.F.ρ'.img * C.D.F.ρ₃.img ≠ C.D.F.ρ₃.img * C.D.F.ρ'.img :=
    C.D.c.noncomm C.D.F.ρ' C.D.F.ρ₃ C.D.F.hne₂ C.D.F.hn₂
  have key : ∀ x : NQuot (W ⊔ OCW W), q * x * q⁻¹ = x →
      x * C.D.F.ρ₃.img ≠ C.D.F.ρ₃.img * x → σ.img * x ≠ x * σ.img := by
    intro x hx hne h
    apply hne
    rw [hσ] at h
    have e : q * (x * C.D.F.ρ₃.img) * q⁻¹ = q * (C.D.F.ρ₃.img * x) * q⁻¹ := by
      calc q * (x * C.D.F.ρ₃.img) * q⁻¹ = (q * x * q⁻¹) * (q * C.D.F.ρ₃.img * q⁻¹) := by group
        _ = x * (q * C.D.F.ρ₃.img * q⁻¹) := by rw [hx]
        _ = (q * C.D.F.ρ₃.img * q⁻¹) * x := h.symm
        _ = (q * C.D.F.ρ₃.img * q⁻¹) * (q * x * q⁻¹) := by rw [hx]
        _ = q * (C.D.F.ρ₃.img * x) * q⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel e)
  have hσr := key _ hr (fun h => hrs h)
  have hσt := key _ ht (fun h => hts h)
  set a := C.D.φ (T7D.imgQ C.D.F.ρ)
  set b := C.D.φ (T7D.imgQ C.D.F.ρ')
  set c := C.D.φ (T7D.imgQ C.D.F.ρ₃)
  set c' := C.D.φ (T7D.imgQ σ)
  have hab : a ≠ b := fun h => C.D.hab (C.D.φ.injective h)
  have hcomm : a * b = b * a := by rw [← map_mul, ← map_mul, C.D.hcomm]
  have hac : a * c ≠ c * a := by
    intro h; apply C.D.hac; apply C.D.φ.injective; rw [map_mul, map_mul]; exact h
  have hc'a : c' * a ≠ a * c' := by
    intro h; apply hσr; rw [← imgQ_comm_iff]; apply C.D.φ.injective
    rw [map_mul, map_mul]; exact h
  have hc'b : c' * b ≠ b * c' := by
    intro h; apply hσt; rw [← imgQ_comm_iff]; apply C.D.φ.injective
    rw [map_mul, map_mul]; exact h
  have hval : ∀ X : ↥(muGroup Ω W), c' = C.D.φ X → σ.img = (X : NQuot (W ⊔ OCW W)) :=
    fun X h => congrArg Subtype.val (C.D.φ.injective h)
  have hrr := C.piG_r_sq
  have htt := C.piG_t_sq
  have hrinv : (Thompson.piG W C.D.F.ρ.r)⁻¹ = Thompson.piG W C.D.F.ρ.r :=
    inv_eq_of_mul_eq_one_right hrr
  have htinv : (Thompson.piG W C.D.F.ρ'.r)⁻¹ = Thompson.piG W C.D.F.ρ'.r :=
    inv_eq_of_mul_eq_one_right htt
  rcases S4.swap_word a (C.φ_imgQ_mem _) b (C.φ_imgQ_mem _) c (C.φ_imgQ_mem _) hab hcomm hac c'
      (C.φ_imgQ_mem _) with h | h | h | h | h | h
  · exact absurd (by rw [h]) hc'a
  · exact absurd (by rw [h, hcomm]) hc'a
  · refine ⟨1, ⟨Subgroup.one_mem _, by simp [conjSub_one], by simp [conjSub_one]⟩, ?_⟩
    refine C.fix_J_of hyN (Subgroup.one_mem _) ?_
    rw [← hσ, hval (T7D.imgQ C.D.F.ρ₃) h, Thompson.piG_of_mem_sup (Subgroup.one_mem _)]
    simp [T7D.imgQ]
  · refine ⟨C.D.F.ρ.r, C.good_r, C.fix_J_of hyN C.D.F.ρ.r_mem_normalizer ?_⟩
    rw [← hσ, hval (T7D.imgQ C.D.F.ρ * T7D.imgQ C.D.F.ρ₃ * T7D.imgQ C.D.F.ρ)
      (by rw [h, map_mul, map_mul]), hrinv]
    rfl
  · refine ⟨C.D.F.ρ'.r, C.good_t, C.fix_J_of hyN C.D.F.ρ'.r_mem_normalizer ?_⟩
    rw [← hσ, hval (T7D.imgQ C.D.F.ρ' * T7D.imgQ C.D.F.ρ₃ * T7D.imgQ C.D.F.ρ')
      (by rw [h, map_mul, map_mul]), htinv]
    rfl
  · refine ⟨C.D.F.ρ.r * C.D.F.ρ'.r, good_mul C.good_r C.good_t,
      C.fix_J_of hyN (Subgroup.mul_mem _ C.D.F.ρ.r_mem_normalizer C.D.F.ρ'.r_mem_normalizer) ?_⟩
    rw [← hσ, hval (T7D.imgQ C.D.F.ρ * T7D.imgQ C.D.F.ρ' * T7D.imgQ C.D.F.ρ₃ *
        T7D.imgQ C.D.F.ρ' * T7D.imgQ C.D.F.ρ) (by rw [h, map_mul, map_mul, map_mul, map_mul]),
      Thompson.piG_mul C.D.F.ρ.r_mem_normalizer C.D.F.ρ'.r_mem_normalizer, mul_inv_rev, hrinv,
      htinv]
    change C.D.F.ρ.img * C.D.F.ρ'.img * C.D.F.ρ₃.img * C.D.F.ρ'.img * C.D.F.ρ.img = _
    unfold Thompson.Rep.img
    group

include C in
theorem exists_decomp {y : G} (hy : y ∈ (S : Subgroup G)) :
    ∃ x ∈ (S : Subgroup G) ⊓ MGrp Ω W, ∃ t ∈ (S : Subgroup G), TrivMu Ω W t ∧ y = x * t := by
  obtain ⟨x₀, hx₀P, hx₀K⟩ : ∃ x₀ ∈ (S : Subgroup G) ⊓ MGrp Ω W, conjSub (x₀⁻¹ * y) K = K := by
    rcases C.conjSub_K_mem hy with h | h
    · exact ⟨1, Subgroup.one_mem _, by rw [inv_one, one_mul, h]⟩
    · obtain ⟨x₀, hx₀P, hx₀⟩ := C.exists_swap
      refine ⟨x₀, hx₀P, ?_⟩
      rw [conjSub_mul, h, ← hx₀, conjSub_inv_conjSub]
  set y₁ := x₀⁻¹ * y with hy₁
  have hy₁S : y₁ ∈ (S : Subgroup G) := Subgroup.mul_mem _ (Subgroup.inv_mem _ hx₀P.1) hy
  have hy₁K' : conjSub y₁ K' = K' := C.conjSub_K'_of_K hx₀K
  obtain ⟨w, hw, hwJ⟩ := C.exists_fix_J hy₁S hx₀K hy₁K'
  refine ⟨x₀ * w, Subgroup.mul_mem _ hx₀P hw.1, w⁻¹ * y₁,
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hw.1.1) hy₁S, ?_, by rw [hy₁]; group⟩
  have hwK : conjSub w⁻¹ K = K := by
    conv_lhs => rw [← hw.2.1]
    exact conjSub_inv_conjSub w K
  have hwK' : conjSub w⁻¹ K' = K' := by
    conv_lhs => rw [← hw.2.2]
    exact conjSub_inv_conjSub w K'
  have htN : w⁻¹ * y₁ ∈ Subgroup.normalizer (W : Set G) :=
    C.le_normalizer_W (Subgroup.mul_mem _ (Subgroup.inv_mem _ hw.1.1) hy₁S)
  refine C.trivMu_of_fix htN ?_ ?_ hwJ
  · rw [C.hK, conjSub_mul, hx₀K, hwK]
  · rw [C.hK', conjSub_mul, hy₁K', hwK']

end
end Ctx8Frame
end S24B
end Asc77

end CFSG.ClassicalInvolution.Q3.Q3T8
