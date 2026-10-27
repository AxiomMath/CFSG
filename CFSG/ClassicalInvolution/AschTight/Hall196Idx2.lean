module

public import CFSG.ClassicalInvolution.AschTight.Hall196Idx
public import CFSG.ClassicalInvolution.AschTight.Hall196Basic
public import CFSG.ClassicalInvolution.AschTight.Hall196Wr3
public import CFSG.ClassicalInvolution.AschTight.S1916Basic
public import CFSG.ClassicalInvolution.AschTight.S1911EtaY3
public import CFSG.ClassicalInvolution.AschTight.Sec19DataT

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Hall196

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.GorensteinWalter
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G} {F : Type} [Field F]
  [Finite F] {p f : ℕ} [Fact p.Prime]

theorem mem_sec19Y_iff (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, F))
    (hFcard : Nat.card F = p ^ f) (hF : IsOddPrimePower (Nat.card F)) (h3 : 3 < Nat.card F)
    {x : G} (hx : x ∈ Subgroup.normalizer (K : Set G)) :
    x ∈ sec19Y K z ↔ x ∈ sec19X K z ∧ normalizerToPGammaL2Mod e hFcard hF h3 ⟨x, hx⟩ = 1 := by
  rw [normalizerToPGammaL2Mod_eq_one_iff]
  constructor
  · rintro ⟨hxX, -, -, hc⟩
    exact ⟨hxX, hc⟩
  · rintro ⟨hxX, hc⟩
    exact ⟨hxX, hx, AschTight.mem_normalizer_oddCoreOf_of_mem_normalizer hx, hc⟩

theorem subgroupOf_sup_sec19Y_eq (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, F))
    (hFcard : Nat.card F = p ^ f) (hF : IsOddPrimePower (Nat.card F)) (h3 : 3 < Nat.card F)
    (hKX : K ≤ sec19X K z) (hXN : sec19X K z ≤ Subgroup.normalizer (K : Set G)) :
    (K ⊔ sec19Y K z).subgroupOf (Subgroup.normalizer (K : Set G)) =
      (pGammaL2PSLRange F).comap (normalizerToPGammaL2Mod e hFcard hF h3) ⊓
        (sec19X K z).subgroupOf (Subgroup.normalizer (K : Set G)) := by
  set N := Subgroup.normalizer (K : Set G) with hN
  set Ψ := normalizerToPGammaL2Mod e hFcard hF h3 with hΨ
  have hYX : sec19Y K z ≤ sec19X K z := fun _ hx => hx.1
  apply le_antisymm
  · have hle : K ⊔ sec19Y K z ≤ ((pGammaL2PSLRange F).comap Ψ).map N.subtype := by
      refine sup_le (fun k hk => ⟨⟨k, Subgroup.le_normalizer hk⟩, ?_, rfl⟩) (fun y hy => ?_)
      · exact normalizerToPGammaL2Mod_mem_pGammaL2PSLRange e hFcard hF h3 hk
      · have hyN := hXN (hYX hy)
        refine ⟨⟨y, hyN⟩, ?_, rfl⟩
        change Ψ ⟨y, hyN⟩ ∈ pGammaL2PSLRange F
        rw [((mem_sec19Y_iff e hFcard hF h3 hyN).mp hy).2]
        exact (pGammaL2PSLRange F).one_mem
    intro x hx
    refine ⟨?_, Subgroup.mem_subgroupOf.mpr (sup_le hKX hYX (Subgroup.mem_subgroupOf.mp hx))⟩
    obtain ⟨y, hy, hyx⟩ := hle (Subgroup.mem_subgroupOf.mp hx)
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy
  · rintro x ⟨hxP, hxX⟩
    have hxP' : Ψ x ∈ (K.subgroupOf N).map Ψ := by
      rw [map_subgroupOf_eq_pGammaL2PSLRange]
      exact hxP
    obtain ⟨k, hk, hkx⟩ := hxP'
    have hk' : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hk
    have h1 : Ψ (k⁻¹ * x) = 1 := by rw [map_mul, map_inv, hkx, inv_mul_cancel]
    have h2 : ((k⁻¹ * x : N) : G) ∈ sec19Y K z := by
      refine (mem_sec19Y_iff e hFcard hF h3 (k⁻¹ * x).2).mpr ⟨?_, h1⟩
      exact (sec19X K z).mul_mem ((sec19X K z).inv_mem (hKX hk'))
        (Subgroup.mem_subgroupOf.mp hxX)
    have e1 : (x : G) = k * ((k⁻¹ * x : N) : G) := by simp
    refine Subgroup.mem_subgroupOf.mpr ?_
    rw [e1]
    exact (K ⊔ sec19Y K z).mul_mem (Subgroup.mem_sup_left hk') (Subgroup.mem_sup_right h2)

omit [Finite G] in
theorem isSylow2In_subgroupOf_of_le {Y T J : Subgroup G} (h : IsSylow2In T J) (hJY : J ≤ Y) :
    IsSylow2In (T.subgroupOf Y) (J.subgroupOf Y) := by
  refine ⟨fun x hx => Subgroup.mem_subgroupOf.mpr (h.1 (Subgroup.mem_subgroupOf.mp hx)),
    h.2.1.comap_subtype, fun V' hV'J hV'2 hle => ?_⟩
  have h1 : V'.map Y.subtype = T := by
    refine h.2.2 _ ?_ (hV'2.map _) ?_
    · rintro _ ⟨v, hv, rfl⟩
      exact Subgroup.mem_subgroupOf.mp (hV'J hv)
    · intro x hx
      exact ⟨⟨x, hJY (h.1 hx)⟩, hle (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  rw [← h1]
  exact (Subgroup.comap_map_eq_self_of_injective Y.subtype_injective V').symm

theorem not_map_le_pGammaL2PSLRange [IsSimpleGroup G] {S : Sylow 2 G} {W L : Subgroup G} {t : G}
    {V : Subgroup G} (hDT : Sec19DataT p f K z S W L t V)
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, F)) (hFcard : Nat.card F = p ^ f)
    (hF : IsOddPrimePower (Nat.card F)) (h3 : 3 < Nat.card F) :
    ¬ (V.subgroupOf (Subgroup.normalizer (K : Set G))).map
        (normalizerToPGammaL2Mod e hFcard hF h3) ≤ pGammaL2PSLRange F := by
  intro hle
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (PGammaL2 F) := finite_pGammaL2
  have hd := hDT.toSec19Data
  have htb := hd.tight.toTightBranch
  have hI := isUniqueInvolution_of_tight htb
  have hNC := normalizer_eq_centralizer_of_tight htb
  set N := Subgroup.normalizer (K : Set G) with hN
  set Ψ := normalizerToPGammaL2Mod e hFcard hF h3 with hΨ
  set R : Subgroup G := (S : Subgroup G) ⊓ K with hR
  have hKN : K ≤ N := Subgroup.le_normalizer
  have hVN : V ≤ N := le_normalizer_of_sec19DataT hDT
  have hRK : R ≤ K := inf_le_right
  have hR2 : IsPGroup 2 R := S.isPGroup'.to_le inf_le_left
  have hRsyl : IsSylow2In R K := isSylow2In_inf_of_le_normalizer S (hd.hSz.trans hNC.ge)
  have hncomm := exists_ne_comm_of_mem_rSet hd.tight.branch.odd hd.tight.branch.five
    hd.tight.branch.member (inf_mem_rSet hd)
  have hR'syl : IsSylow2In (R.subgroupOf N) (K.subgroupOf N) :=
    isSylow2In_subgroupOf_of_le hRsyl hKN
  have hQsyl := isSylow2In_map_hom Ψ hR'syl
  rw [map_subgroupOf_eq_pGammaL2PSLRange] at hQsyl
  have h8 : 8 ≤ Nat.card R := hncomm.2
  have hzR : z ∈ R := AscL62.mem_of_uniqueInvolution_of_pGroup hI hRK hR2 (by omega)
  have hzΨ : Ψ ⟨z, hKN hI.mem⟩ = 1 := by
    rw [normalizerToPGammaL2Mod_eq_one_iff]
    intro l hl
    have hc : z * l * z⁻¹ * l⁻¹ = 1 := by
      rw [hI.commute_of_mem hl]
      group
    rw [commutatorElement_def, hc]
    exact (Asc77.oddCoreOf K).one_mem
  have hQcard : 2 * Nat.card ↥((R.subgroupOf N).map Ψ) ≤ Nat.card R := by
    have h1 := Subgroup.card_ker_mul_card_range (Ψ.comp (R.subgroupOf N).subtype)
    rw [MonoidHom.range_comp, Subgroup.range_subtype,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hRK.trans hKN)).toEquiv] at h1
    have h2 : 2 ≤ Nat.card (Ψ.comp (R.subgroupOf N).subtype).ker := by
      apply (Subgroup.one_lt_card_iff_ne_bot _).mpr
      intro hbot
      have hmem : (⟨⟨z, hKN hI.mem⟩, Subgroup.mem_subgroupOf.mpr hzR⟩ : ↥(R.subgroupOf N)) ∈
          (Ψ.comp (R.subgroupOf N).subtype).ker := hzΨ
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hI.ne_one (congrArg (fun x : ↥(R.subgroupOf N) => ((x : N) : G)) hmem)
    rw [← h1]
    exact Nat.mul_le_mul_right _ h2
  have ef := S1911.etaYForm p f G K z S W L t V hDT
  have hVker : V.subgroupOf N ⊓ Ψ.ker = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxV, hxk⟩
    have hxV' : (x : G) ∈ V := Subgroup.mem_subgroupOf.mp hxV
    have hxY : (x : G) ∈ sec19Y K z :=
      (mem_sec19Y_iff e hFcard hF h3 x.2).mpr ⟨hDT.leW.trans (S1911.le_sec19X hd) hxV', hxk⟩
    have hxVY : (x : G) ∈ V ⊓ sec19Y K z := ⟨hxV', hxY⟩
    rw [ef.disj, Subgroup.mem_bot] at hxVY
    exact (Subgroup.mem_bot).mpr (Subtype.ext hxVY)
  have hVcard : Nat.card ↥((V.subgroupOf N).map Ψ) = Nat.card V := by
    rw [card_map_of_inf_ker_eq_bot Ψ hVker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVN).toEquiv
  have hRV : Nat.card R = 2 * Nat.card V := by
    rw [S1911.card_inf_eq hd, S1911.card_inf_eq_card hDT]
  have hV2 : IsPGroup 2 ↥((V.subgroupOf N).map Ψ) :=
    ((S.isPGroup'.to_le (hDT.leW.trans hd.hWS)).comap_subtype (K := N)).map Ψ
  have hVsyl : IsSylow2In ((V.subgroupOf N).map Ψ) (pGammaL2PSLRange F) :=
    IsSylow2In.of_natCard_le hQsyl hV2 hle (by omega)
  obtain ⟨x, -, hx⟩ := exists_conjSub_eq_of_isSylow2In hQsyl hVsyl
  obtain ⟨-, -, -, hVcyc, -⟩ := hDT.memV
  have hV'cyc : IsCyclic ↥(V.subgroupOf N) :=
    (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hVN)).mpr hVcyc
  have hΨVcyc : IsCyclic ↥((V.subgroupOf N).map Ψ) :=
    isCyclic_of_surjective (Ψ.subgroupMap _) (MonoidHom.subgroupMap_surjective Ψ _)
  rw [← hx] at hΨVcyc
  have hQcyc : IsCyclic ↥((R.subgroupOf N).map Ψ) :=
    (MulEquiv.isCyclic (Subgroup.equivMapOfInjective _ _ (MulAut.conj x).injective)).mpr hΨVcyc
  have hcomm : IsMulCommutative ↥(R.subgroupOf N) := by
    refine (Ψ.subgroupMap (R.subgroupOf N)).isMulCommutative_of_isCyclic_of_ker_le_center ?_
    intro r hr
    have hr1 : Ψ r = 1 := congrArg Subtype.val hr
    have hrc := (normalizerToPGammaL2Mod_eq_one_iff e hFcard hF h3 r).mp hr1
    rw [Subgroup.mem_center_iff]
    intro y
    have hyR : ((y : N) : G) ∈ R := Subgroup.mem_subgroupOf.mp y.2
    have hrR : ((r : N) : G) ∈ R := Subgroup.mem_subgroupOf.mp r.2
    have h1 : ⁅((r : N) : G), ((y : N) : G)⁆ ∈ R ⊓ Asc77.oddCoreOf K := by
      refine ⟨?_, hrc _ (hRK hyR)⟩
      rw [commutatorElement_def]
      exact R.mul_mem (R.mul_mem (R.mul_mem hrR hyR) (R.inv_mem hrR)) (R.inv_mem hyR)
    rw [S1916.inf_oddCoreOf_eq_bot hR2 K, Subgroup.mem_bot, commutatorElement_def] at h1
    apply Subtype.ext
    apply Subtype.ext
    change ((y : N) : G) * ((r : N) : G) = ((r : N) : G) * ((y : N) : G)
    calc ((y : N) : G) * ((r : N) : G) =
        (((r : N) : G) * ((y : N) : G) * ((r : N) : G)⁻¹ * ((y : N) : G)⁻¹)⁻¹ *
          (((r : N) : G) * ((y : N) : G)) := by group
      _ = ((r : N) : G) * ((y : N) : G) := by rw [h1, inv_one, one_mul]
  obtain ⟨⟨a, ha, b, hb, hab⟩, -⟩ := hncomm
  apply hab
  have := hcomm.is_comm.comm (⟨⟨a, hKN (hRK ha)⟩, Subgroup.mem_subgroupOf.mpr ha⟩ :
    ↥(R.subgroupOf N)) ⟨⟨b, hKN (hRK hb)⟩, Subgroup.mem_subgroupOf.mpr hb⟩
  exact congrArg (fun x : ↥(R.subgroupOf N) => ((x : N) : G)) this

omit [Finite F] in
theorem exists_data_of_tightBranchD (ht : S19R.TightStd p f K z) :
    Nonempty (K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)) ∧
      Nat.card (GaloisField p f) = p ^ f ∧ IsOddPrimePower (Nat.card (GaloisField p f)) ∧
      3 < Nat.card (GaloisField p f) := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    have := ht.branch.five
    simp at this
  have hFcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf0
  refine ⟨ht.branch.member.nonempty_equiv, hFcard, ⟨p, f, Fact.out,
    Nat.Prime.odd_of_ne_two Fact.out ht.branch.odd, Nat.one_le_iff_ne_zero.mpr hf0, hFcard⟩, ?_⟩
  have := ht.branch.five
  omega

theorem map_sec19X_eq_pGammaL2PGLRange_of_sec19DataT [IsSimpleGroup G] {S : Sylow 2 G}
    {W L : Subgroup G} {t : G} {V : Subgroup G} (hDT : Sec19DataT p f K z S W L t V)
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f))
    (hFcard : Nat.card (GaloisField p f) = p ^ f)
    (hF : IsOddPrimePower (Nat.card (GaloisField p f))) (h3 : 3 < Nat.card (GaloisField p f)) :
    ((sec19X K z).subgroupOf (Subgroup.normalizer (K : Set G))).map
      (normalizerToPGammaL2Mod e hFcard hF h3) = pGammaL2PGLRange (GaloisField p f) := by
  have hd := hDT.toSec19Data
  have ht := hd.tight
  set N := Subgroup.normalizer (K : Set G) with hN
  set Ψ := normalizerToPGammaL2Mod e hFcard hF h3 with hΨ
  have hKX : K ≤ sec19X K z := S1916.le_sec19X ht.branch.member
  have hVX : V ≤ sec19X K z := hDT.leW.trans (S1911.le_sec19X hd)
  have hV5 := not_map_le_pGammaL2PSLRange hDT e hFcard hF h3
  have h5 := c19_5Tmp_of_l6_2 p f (l6_2ModTmp p f)
  have hXle : ((sec19X K z).subgroupOf N).map Ψ ≤ pGammaL2PGLRange (GaloisField p f) := by
    rintro _ ⟨x, hx, rfl⟩
    refine h5 G K z ht e hFcard hF h3 x ?_
    rw [xGroup_eq_gammaGen]
    exact Subgroup.mem_subgroupOf.mp hx
  have hsub : ∀ {A : Subgroup G}, A ≤ sec19X K z → A.subgroupOf N ≤ (sec19X K z).subgroupOf N :=
    fun hA _ hx => Subgroup.mem_subgroupOf.mpr (hA (Subgroup.mem_subgroupOf.mp hx))
  have hPSLX : pGammaL2PSLRange (GaloisField p f) ≤ ((sec19X K z).subgroupOf N).map Ψ := by
    rw [← map_subgroupOf_eq_pGammaL2PSLRange e hFcard hF h3]
    exact Subgroup.map_mono (hsub hKX)
  exact eq_of_relIndex_eq_two hPSLX hXle (pGammaL2_psl_range_relIndex_pgl_eq_two _ hF)
    fun h => hV5 ((Subgroup.map_mono (hsub hVX)).trans h)

theorem map_sec19X_eq_pGammaL2PGLRange [IsSimpleGroup G] {S : Sylow 2 G} {W : Subgroup G}
    (hd : Sec19Data p f K z S W) (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f))
    (hFcard : Nat.card (GaloisField p f) = p ^ f)
    (hF : IsOddPrimePower (Nat.card (GaloisField p f))) (h3 : 3 < Nat.card (GaloisField p f)) :
    ((sec19X K z).subgroupOf (Subgroup.normalizer (K : Set G))).map
      (normalizerToPGammaL2Mod e hFcard hF h3) = pGammaL2PGLRange (GaloisField p f) := by
  obtain ⟨L, t, V, hDT⟩ := exists_sec19DataT hd
  exact map_sec19X_eq_pGammaL2PGLRange_of_sec19DataT hDT e hFcard hF h3

theorem relIndex_sup_sec19Y_of_sec19DataT [IsSimpleGroup G] {S : Sylow 2 G} {W L : Subgroup G}
    {t : G} {V : Subgroup G} (hDT : Sec19DataT p f K z S W L t V) :
    (K ⊔ sec19Y K z).relIndex (sec19X K z) = 2 ∧ ¬ V ≤ K ⊔ sec19Y K z ∧
      K ⊔ sec19Y K z ⊔ V = sec19X K z := by
  have hd := hDT.toSec19Data
  have ht := hd.tight
  obtain ⟨⟨e⟩, hFcard, hF, h3⟩ := exists_data_of_tightBranchD ht
  set N := Subgroup.normalizer (K : Set G) with hN
  set Ψ := normalizerToPGammaL2Mod e hFcard hF h3 with hΨ
  have hNC := normalizer_eq_centralizer_of_tight ht.toTightBranch
  have hXN : sec19X K z ≤ N := (gammaGen_le_centralizer _ z).trans hNC.ge
  have hKX : K ≤ sec19X K z := S1916.le_sec19X ht.branch.member
  have hYX : sec19Y K z ≤ sec19X K z := sec19Y_le_sec19X K z
  have hVX : V ≤ sec19X K z := hDT.leW.trans (S1911.le_sec19X hd)
  have hKY := subgroupOf_sup_sec19Y_eq e hFcard hF h3 hKX hXN
  have hV5 := not_map_le_pGammaL2PSLRange hDT e hFcard hF h3
  have hXeq := map_sec19X_eq_pGammaL2PGLRange_of_sec19DataT hDT e hFcard hF h3
  have hidx : (K ⊔ sec19Y K z).relIndex (sec19X K z) = 2 := by
    rw [← Subgroup.relIndex_subgroupOf hXN, hKY, Subgroup.inf_relIndex_right,
      Subgroup.relIndex_comap, hXeq]
    exact pGammaL2_psl_range_relIndex_pgl_eq_two _ hF
  have hnot : ¬ V ≤ K ⊔ sec19Y K z := by
    intro hVKY
    apply hV5
    rintro _ ⟨v, hv, rfl⟩
    have hv' : v ∈ (K ⊔ sec19Y K z).subgroupOf N :=
      Subgroup.mem_subgroupOf.mpr (hVKY (Subgroup.mem_subgroupOf.mp hv))
    rw [hKY] at hv'
    exact hv'.1
  exact ⟨hidx, hnot, eq_of_relIndex_eq_two le_sup_left (sup_le (sup_le hKX hYX) hVX) hidx
    fun h => hnot (le_sup_right.trans h)⟩

theorem relIndex_sup_sec19Y [IsSimpleGroup G] {S : Sylow 2 G} {W : Subgroup G}
    (hd : Sec19Data p f K z S W) : (K ⊔ sec19Y K z).relIndex (sec19X K z) = 2 := by
  obtain ⟨L, t, V, hDT⟩ := exists_sec19DataT hd
  exact (relIndex_sup_sec19Y_of_sec19DataT hDT).1

end CFSG.ClassicalInvolution.Disconnected.AschTight.Hall196
