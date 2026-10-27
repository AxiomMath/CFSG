module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P5IiiBase
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL630Apply
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yCommon
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL630Setup

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M : Subgroup G} {x z : G}
  {T : Subgroup G} {f : ℕ}

theorem centralizer_singleton_le_of_involution3 (hL : L630Setting3 G P M x z T f)
    {c : G} (hcS : c ∈ smallRankS x T) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (hzc : z * c = c * z) :
    centralizer ({c} : Set G) ≤ M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne : zpowers c ≠ ⊥ := zpowers_eq_bot.not.mpr hc1
  have hcz : z ∈ centralizer ({c} : Set G) := mem_centralizer_singleton_iff.mpr hzc
  have hzN : zpowers z ≤ normalizer ((zpowers c : Subgroup G) : Set G) :=
    zpowers_le.mpr (centralizer_singleton_le_normalizer_zpowers c hcz)
  have hH : normalizer ((zpowers c : Subgroup G) : Set G) ≤ M :=
    hL.prop614 (zpowers c) (zpowers_le.mpr hcS) hne hzN
  intro g hg
  exact hH (centralizer_singleton_le_normalizer_zpowers c hg)

theorem stepApplyI2026_holds3 (hL : L630Setting3 G P M x z T f)
    (hzN : z ∈ normalizer ((smallRankF 5 f x : Subgroup G) : Set G)) :
    zpowers (Subgroup.normalizerMonoidHom (smallRankF 5 f x) ⟨z, hzN⟩) ≤
        (Subgroup.normalizerMonoidHom (smallRankF 5 f x)).range ∧
      Nat.card (zpowers (Subgroup.normalizerMonoidHom (smallRankF 5 f x) ⟨z, hzN⟩)) = 5 ∧
      ((smallRankR x z T).subgroupOf
          (normalizer ((smallRankF 5 f x : Subgroup G) : Set G))).map
          (Subgroup.normalizerMonoidHom (smallRankF 5 f x)) ≤
          (Subgroup.normalizerMonoidHom (smallRankF 5 f x)).range ∧
      ((smallRankR x z T).subgroupOf
          (normalizer ((smallRankF 5 f x : Subgroup G) : Set G))).map
          (Subgroup.normalizerMonoidHom (smallRankF 5 f x)) ≤
          pCoreOf 2 (Subgroup.normalizerMonoidHom (smallRankF 5 f x)).range ∧
      ⁅((smallRankR x z T).subgroupOf
          (normalizer ((smallRankF 5 f x : Subgroup G) : Set G))).map
          (Subgroup.normalizerMonoidHom (smallRankF 5 f x)),
        zpowers (Subgroup.normalizerMonoidHom (smallRankF 5 f x) ⟨z, hzN⟩)⁆ =
        ((smallRankR x z T).subgroupOf
          (normalizer ((smallRankF 5 f x : Subgroup G) : Set G))).map
          (Subgroup.normalizerMonoidHom (smallRankF 5 f x)) ∧
      smallRankIsQ8D8
        (((smallRankR x z T).subgroupOf
          (normalizer ((smallRankF 5 f x : Subgroup G) : Set G))).map
          (Subgroup.normalizerMonoidHom (smallRankF 5 f x))) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hf5 : Nat.Prime 5 := by norm_num
  have hf : f.Prime := hL.prime
  have hf2 : f ≠ 2 := hL.ne_two
  haveI : Fact f.Prime := ⟨hf⟩
  have hz5 : z ^ 5 = 1 := hL.central.pow_eq_one
  have hz1 : z ≠ 1 := hL.central.ne_one
  have hx : x ∈ (P : Subgroup G) := hL.point.mem
  have hFe : IsElemAbelian f (smallRankF 5 f x) := hL.lemma629.2.2.2.1
  have hFc : Nat.card (smallRankF 5 f x) = f ^ 4 := hL.lemma629.2.2.2.2.1
  have hloc : rankThreeLocalRank f G ≤ 3 := hL.lemma629.2.2.1
  have hRM : smallRankR x z T ≤ pCoreOf 2 M := hL.lemma629.2.1
  have hinvR := hL.lemma629.2.2.2.2.2
  have hQ8 : smallRankIsQ8D8 (smallRankR x z T) := hL.lemma628.2.2.1 rfl
  have hFM : smallRankF 5 f x ⊓ M = ⊥ := smallRankF_inf_eq_bot hf hf2 hL.lemma628.2.2.2
  have hFne : smallRankF 5 f x ≠ ⊥ := by
    intro h
    have hcard := hFc
    rw [h, Subgroup.card_bot] at hcard
    have h4 : 2 ≤ f ^ 4 := le_trans hf.two_le (Nat.le_self_pow (by norm_num) f)
    rw [← hcard] at h4
    norm_num at h4
  have hC_z : centralizer ({z} : Set G) ≤ M := hL.centralizer_z_le
  have hodd : Odd (Nat.card (centralizer (smallRankF 5 f x : Set G))) :=
    odd_card_centralizer_of_rank hf hFe hFc hloc
  haveI : Finite (MulAut (smallRankF 5 f x)) :=
    Finite.of_injective (fun e : MulAut (smallRankF 5 f x) => e.toEquiv)
      (fun a b h => MulEquiv.ext fun y =>
        congrArg (fun e : smallRankF 5 f x ≃ smallRankF 5 f x => e y) h)
  set F : Subgroup G := smallRankF 5 f x with hFdef
  set R : Subgroup G := smallRankR x z T with hRdef
  set S : Subgroup G := smallRankS x T with hSdef
  set N : Subgroup G := normalizer ((F : Subgroup G) : Set G) with hNdef
  set C : Subgroup G := centralizer (F : Set G) with hCdef
  set ψ : N →* MulAut F := Subgroup.normalizerMonoidHom F with hψdef
  set z1 : N := ⟨z, hzN⟩ with hz1def
  have hC_le_N : C ≤ N := Subgroup.centralizer_le_normalizer _
  have hS_le_Cx : S ≤ centralizer ({x} : Set G) := inf_le_right
  have hzS : zpowers z ≤ normalizer (S : Set G) :=
    hL.failure.z_le_normalizer_S
  have hR_le_S : R ≤ S := smallRankR_le_smallRankS hzS
  have hR_le_Cx : R ≤ centralizer ({x} : Set G) := hR_le_S.trans hS_le_Cx
  have hR_le_N : R ≤ N := fun r hr => mem_normalizer_smallRankF hf5 hf (hR_le_Cx hr)
  have hzR : z ∈ normalizer (R : Set G) := zpowers_le_normalizer_smallRankR (mem_zpowers z)
  have hS2 : IsPGroup 2 S := hL.sylowTwo.isPGroup.to_inf_left
  have hcomp : ¬ 5 ∣ Nat.card S := not_five_dvd_card_of_isPGroup_two hS2
  have hpg : IsPGroup 5 (zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hz5 hz1]; norm_num)
  have hRz : ⁅R, zpowers z⁆ = R := commutator_smallRankR_zpowers hpg hcomp hzS
  have hRp : IsPGroup 2 R := (pCoreOf_isPGroup 2 M).to_le hRM
  have hRC : R ⊓ C = ⊥ :=
    inf_centralizer_eq_bot_of_inverts hf hf2 (fun e he => hFe.2 e he) hFne hRp hR_le_N hinvR
  obtain ⟨c, hcR, hc1, hc2, hcc⟩ := exists_central_involution_of_Q8D8 hQ8
  have hcZ : c ∈ smallRankCenter R := by
    rw [smallRankCenter, Subgroup.mem_inf]
    exact ⟨hcR, mem_centralizer_iff.mpr fun r hr => (hcc r hr).symm⟩
  have hcinv : ∀ a ∈ F, c * a * c⁻¹ = a⁻¹ := hinvR c hcZ hc1
  have hcC : c ∉ C := by
    intro hc
    have hmem : c ∈ R ⊓ C := ⟨hcR, hc⟩
    rw [hRC, Subgroup.mem_bot] at hmem
    exact hc1 hmem
  have hzc : z * c * z⁻¹ = c := conj_fixes_central_involution hzR hcR hc1 hc2 hcc hinvR hRC
  have hzc' : z * c = c * z := by
    calc z * c = z * c * z⁻¹ * z := by group
      _ = c * z := by rw [hzc]
  have hC_c : centralizer ({c} : Set G) ≤ M :=
    centralizer_singleton_le_of_involution3 hL (hR_le_S hcR) hc2 hc1 hzc'
  have hψapp : ∀ (g : N) (a : F), ((ψ g a : F) : G) = (g : G) * (a : G) * (g : G)⁻¹ :=
    fun g a => rfl
  have hker : ∀ g : N, ψ g = 1 ↔ (g : G) ∈ C := by
    intro g
    constructor
    · intro h
      rw [mem_centralizer_iff]
      intro a ha
      have h1 : (g : G) * a * (g : G)⁻¹ = a := by
        have := hψapp g ⟨a, ha⟩
        rw [h, MulAut.one_apply] at this
        exact this.symm
      calc (a : G) * (g : G) = ((g : G) * (a : G) * (g : G)⁻¹) * (g : G) := by rw [h1]
        _ = (g : G) * (a : G) := by group
    · intro hg
      ext a
      rw [hψapp, MulAut.one_apply]
      have hc : (a : G) * g = g * a := (mem_centralizer_iff.mp hg) a a.2
      calc (g : G) * (a : G) * (g : G)⁻¹ = ((a : G) * (g : G)) * (g : G)⁻¹ := by rw [← hc]
        _ = (a : G) := by group
  haveI hCn : (C.subgroupOf N).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using conj_mem_centralizer_of_mem_normalizer g.2 hn⟩
  have hodd' : Odd (Nat.card (C.subgroupOf N)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hC_le_N).toEquiv]
    exact hodd
  have hcN : c ∈ N := hR_le_N hcR
  have hc'2 : (⟨c, hcN⟩ : N) ^ 2 = 1 := Subtype.ext (by simpa using hc2)
  have hc'C : (⟨c, hcN⟩ : N) ∉ C.subgroupOf N := fun h => hcC (Subgroup.mem_subgroupOf.mp h)
  have hcinv' : ∀ a ∈ F, c⁻¹ * a * c = a⁻¹ := by
    intro a ha
    have hb : c⁻¹ * a * c ∈ F := (Subgroup.mem_normalizer_iff''.mp hcN a).mp ha
    have h1 := hcinv _ hb
    have h2 : (c⁻¹ * a * c)⁻¹ = a := by
      rw [← h1]
      group
    calc c⁻¹ * a * c = ((c⁻¹ * a * c)⁻¹)⁻¹ := (inv_inv _).symm
      _ = a⁻¹ := by rw [h2]
  have hinv' : ∀ n : N, ∃ e ∈ C.subgroupOf N, n * (⟨c, hcN⟩ : N) * n⁻¹ = e * ⟨c, hcN⟩ := by
    intro n
    have ht : ∀ a ∈ F, ((n : G) * c * (n : G)⁻¹) * a * ((n : G) * c * (n : G)⁻¹)⁻¹ = a⁻¹ := by
      intro a ha
      have ha' : (n : G)⁻¹ * a * (n : G) ∈ F := (Subgroup.mem_normalizer_iff''.mp n.2 a).mp ha
      have h1 := hcinv _ ha'
      calc ((n : G) * c * (n : G)⁻¹) * a * ((n : G) * c * (n : G)⁻¹)⁻¹
          = (n : G) * (c * ((n : G)⁻¹ * a * (n : G)) * c⁻¹) * (n : G)⁻¹ := by group
        _ = (n : G) * ((n : G)⁻¹ * a * (n : G))⁻¹ * (n : G)⁻¹ := by rw [h1]
        _ = a⁻¹ := by group
    have hec : (n : G) * c * (n : G)⁻¹ * c⁻¹ ∈ C := by
      rw [hCdef, mem_centralizer_iff]
      intro a ha
      have key : ((n : G) * c * (n : G)⁻¹ * c⁻¹) * a * ((n : G) * c * (n : G)⁻¹ * c⁻¹)⁻¹ = a := by
        calc ((n : G) * c * (n : G)⁻¹ * c⁻¹) * a * ((n : G) * c * (n : G)⁻¹ * c⁻¹)⁻¹
            = ((n : G) * c * (n : G)⁻¹) * (c⁻¹ * a * c) * ((n : G) * c * (n : G)⁻¹)⁻¹ := by
              group
          _ = ((n : G) * c * (n : G)⁻¹) * a⁻¹ * ((n : G) * c * (n : G)⁻¹)⁻¹ := by
              rw [hcinv' a ha]
          _ = (((n : G) * c * (n : G)⁻¹) * a * ((n : G) * c * (n : G)⁻¹)⁻¹)⁻¹ := by group
          _ = a := by rw [ht a ha, inv_inv]
      calc a * ((n : G) * c * (n : G)⁻¹ * c⁻¹)
          = (((n : G) * c * (n : G)⁻¹ * c⁻¹) * a * ((n : G) * c * (n : G)⁻¹ * c⁻¹)⁻¹) *
              ((n : G) * c * (n : G)⁻¹ * c⁻¹) := by rw [key]
        _ = ((n : G) * c * (n : G)⁻¹ * c⁻¹) * a := by group
    refine ⟨⟨(n : G) * c * (n : G)⁻¹ * c⁻¹,
      N.mul_mem (N.mul_mem (N.mul_mem n.2 hcN) (N.inv_mem n.2)) (N.inv_mem hcN)⟩, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      exact hec
    · apply Subtype.ext
      show (n : G) * c * (n : G)⁻¹ = ((n : G) * c * (n : G)⁻¹ * c⁻¹) * c
      group
  have hfrat := mem_mul_centralizer_of_involution (H := ↥N) (C.subgroupOf N) hodd' hc'2 hc'C hinv'
  have hdec : ∀ g : N, ∃ m : N, ψ g = ψ m ∧ (m : G) ∈ centralizer ({c} : Set G) := by
    intro g
    obtain ⟨d, hd, m, hm, hgm⟩ := hfrat g
    refine ⟨m, ?_, ?_⟩
    · rw [hgm, map_mul, (hker d).mpr (Subgroup.mem_subgroupOf.mp hd), one_mul]
    · rw [mem_centralizer_singleton_iff]
      have h1 : (m : G) * c * (m : G)⁻¹ = c := by
        have := congrArg Subtype.val hm
        simpa using this
      calc (m : G) * c = ((m : G) * c * (m : G)⁻¹) * (m : G) := by group
        _ = c * (m : G) := by rw [h1]
  set W : Subgroup N := (pCoreOf 2 M ⊓ N).subgroupOf N with hWdef
  set Wψ : Subgroup (MulAut F) := W.map ψ with hWψdef
  have hW_mem : ∀ h : N, h ∈ W ↔ (h : G) ∈ pCoreOf 2 M := by
    intro h
    rw [hWdef, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h' => h'.1, fun h' => ⟨h', h.2⟩⟩
  have hR1 : (R.subgroupOf N) ≤ W := by
    intro r hr
    rw [hW_mem]
    exact hRM (Subgroup.mem_subgroupOf.mp hr)
  have hpc_conj : ∀ m : N, (m : G) ∈ M → ∀ h : N, (h : G) ∈ pCoreOf 2 M →
      ((m * h * m⁻¹ : N) : G) ∈ pCoreOf 2 M := by
    intro m hm h hh
    have := (pCoreOf_subgroupOf_normal 2 M).conj_mem (⟨(h : G), pCoreOf_le_self 2 M hh⟩ : M)
      (Subgroup.mem_subgroupOf.mpr hh) (⟨(m : G), hm⟩ : M)
    rw [Subgroup.mem_subgroupOf] at this
    simpa using this
  have hWψ_le : Wψ ≤ ψ.range := Subgroup.map_le_range ψ W
  have hWn : (Wψ.subgroupOf ψ.range).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨γ, hγ⟩ := MonoidHom.mem_range.mp g.2
    obtain ⟨h, hh, hhn⟩ := Subgroup.mem_map.mp hn
    obtain ⟨m, hψm, hmC⟩ := hdec γ
    have hmM : (m : G) ∈ M := hC_c hmC
    have hmem : m * h * m⁻¹ ∈ W := (hW_mem _).mpr (hpc_conj m hmM h ((hW_mem h).mp hh))
    refine Subgroup.mem_map.mpr ⟨m * h * m⁻¹, hmem, ?_⟩
    show ψ (m * h * m⁻¹) = (g : MulAut F) * (n : MulAut F) * (g : MulAut F)⁻¹
    rw [← hγ, ← hhn, hψm, map_mul, map_mul, map_inv]
  have hpN : IsPGroup 2 (↥(pCoreOf 2 M ⊓ N : Subgroup G)) :=
    (pCoreOf_isPGroup 2 M).to_inf_left
  have hWp2 : IsPGroup 2 W := hpN.comap_subtype
  have hWψp2 : IsPGroup 2 Wψ := hWp2.map ψ
  have hWψ_core : Wψ ≤ pCoreOf 2 ψ.range := le_pCoreOf hWψ_le hWn hWψp2
  have hR1_core : (R.subgroupOf N).map ψ ≤ pCoreOf 2 ψ.range :=
    (Subgroup.map_mono hR1).trans hWψ_core
  have hcommN : ⁅R.subgroupOf N, zpowers z1⁆ = R.subgroupOf N := by
    apply Subgroup.map_injective (f := N.subtype) N.subtype_injective
    rw [Subgroup.map_commutator, MonoidHom.map_zpowers, Subgroup.map_subgroupOf_eq_of_le hR_le_N]
    exact hRz
  have hcommψ : ⁅(R.subgroupOf N).map ψ, zpowers (ψ z1)⁆ = (R.subgroupOf N).map ψ := by
    rw [← MonoidHom.map_zpowers, ← Subgroup.map_commutator, hcommN]
  have hψz1 : ψ z1 ≠ 1 := by
    intro h
    have hzC : z ∈ C := (hker z1).mp h
    have hFle : F ≤ M := fun a ha =>
      hC_z (mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hzC a ha))
    have h0 : F ⊓ M = F := inf_eq_left.mpr hFle
    rw [hFM] at h0
    exact hFne h0.symm
  have hpow : (ψ z1) ^ 5 = 1 := by
    rw [← map_pow]
    have h5 : z1 ^ 5 = 1 := Subtype.ext (by simpa using hz5)
    rw [h5, map_one]
  have hcardz : Nat.card (zpowers (ψ z1)) = 5 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hpow hψz1
  have hinjR1 : ∀ u ∈ R.subgroupOf N, ∀ v ∈ R.subgroupOf N, ψ u = ψ v → u = v := by
    intro u hu v hv huv
    have h1 : ψ (u * v⁻¹) = 1 := by rw [map_mul, map_inv, huv, mul_inv_cancel]
    have h2 : ((u * v⁻¹ : N) : G) ∈ C := (hker _).mp h1
    have h3 : ((u * v⁻¹ : N) : G) ∈ R :=
      R.mul_mem (Subgroup.mem_subgroupOf.mp hu) (R.inv_mem (Subgroup.mem_subgroupOf.mp hv))
    have h4 : ((u * v⁻¹ : N) : G) ∈ R ⊓ C := ⟨h3, h2⟩
    rw [hRC, Subgroup.mem_bot] at h4
    exact mul_inv_eq_one.mp (Subtype.ext h4)
  have hQ8R1 : smallRankIsQ8D8 (R.subgroupOf N) := by
    apply smallRankIsQ8D8_of_map N.subtype N.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hR_le_N]
    exact hQ8
  have hQ8ψ : smallRankIsQ8D8 ((R.subgroupOf N).map ψ) :=
    smallRankIsQ8D8_map_of_injOn ψ (R.subgroupOf N) hinjR1 hQ8R1
  refine ⟨zpowers_le.mpr (MonoidHom.mem_range.mpr ⟨z1, rfl⟩), hcardz,
    Subgroup.map_le_range ψ (R.subgroupOf N), hR1_core, hcommψ, hQ8ψ⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
