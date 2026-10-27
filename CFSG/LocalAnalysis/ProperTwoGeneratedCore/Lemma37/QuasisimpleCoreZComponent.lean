module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreYBasic
public import CFSG.GroupTheory.ThompsonAxB
public import CFSG.Permutation.FiveTransitive.CyclicTwoAutomorphismKernel

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

variable {X : Type} [Group X] [Finite X]

theorem mem_centralizer_of_odd_of_isCyclic {C : Subgroup X} (hC2 : IsPGroup 2 C)
    (hCc : IsCyclic C) {g : X} (hg : g ∈ Subgroup.normalizer (C : Set X))
    (hodd : Odd (orderOf g)) : g ∈ Subgroup.centralizer (C : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAut : IsPGroup 2 (MulAut C) :=
    CFSG.FiveTransitive.CyclicTwoAutomorphismKernel.automorphism_two_group hC2
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hAut (C.normalizerMonoidHom ⟨g, hg⟩)
  have hdvd : orderOf (C.normalizerMonoidHom ⟨g, hg⟩) ∣ orderOf g := by
    have h := orderOf_map_dvd C.normalizerMonoidHom (⟨g, hg⟩ : Subgroup.normalizer (C : Set X))
    rwa [Subgroup.orderOf_mk] at h
  have h1 : orderOf (C.normalizerMonoidHom ⟨g, hg⟩) = 1 := by
    rw [hk] at hdvd ⊢
    rcases k with _ | k
    · rfl
    · exact absurd ((dvd_pow_self 2 k.succ_ne_zero).trans hdvd) hodd.not_two_dvd_nat
  have hker : (⟨g, hg⟩ : Subgroup.normalizer (C : Set X)) ∈ C.normalizerMonoidHom.ker :=
    orderOf_eq_one_iff.mp h1
  rw [Subgroup.normalizerMonoidHom_ker] at hker
  exact Subgroup.mem_subgroupOf.mp hker

theorem mem_centralizer_of_odd_of_rank_one {R : Subgroup X} [R.Normal] (hR2 : IsPGroup 2 R)
    (hinv : ∀ a ∈ R, ∀ b ∈ R, orderOf a = 2 → orderOf b = 2 → a = b) {v : X} (hvR : v ∈ R)
    (hv4 : orderOf v = 4) (hvn : (Subgroup.zpowers v).Normal) {g : X}
    (hodd : Odd (orderOf g)) : g ∈ Subgroup.centralizer (R : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hv2 : IsPGroup 2 (Subgroup.zpowers v) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hv4]; norm_num)
  have hgv : g * v = v * g := by
    have h := mem_centralizer_of_odd_of_isCyclic hv2 (Subgroup.isCyclic_zpowers v)
      (by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top g) hodd
    exact (Subgroup.mem_centralizer_iff.mp h v (Subgroup.mem_zpowers v)).symm
  set C := R ⊓ Subgroup.centralizer ({v} : Set X) with hC
  have hC2 : IsPGroup 2 C := hR2.to_le inf_le_left
  have hvC : v ∈ C := ⟨hvR, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hCc : IsCyclic C := isCyclic_of_forall_eq_of_central hC2
    (fun a ha b hb => hinv a ha.1 b hb.1) hvC
    (fun r hr => Subgroup.mem_centralizer_singleton_iff.mp hr.2) hv4
  have hinvv : ∀ x : X, x * v = v * x → x⁻¹ * v = v * x⁻¹ := fun x hxv => by
    calc x⁻¹ * v = x⁻¹ * (v * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * v) * x⁻¹ := by rw [hxv]
      _ = v * x⁻¹ := by group
  have hconj : ∀ x : X, x * v = v * x → ∀ c ∈ C, x * c * x⁻¹ ∈ C := by
    intro x hxv c hc
    refine ⟨(inferInstance : R.Normal).conj_mem c hc.1 x,
      Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have hcv : c * v = v * c := Subgroup.mem_centralizer_singleton_iff.mp hc.2
    calc x * c * x⁻¹ * v = x * c * (x⁻¹ * v) := by group
      _ = x * c * (v * x⁻¹) := by rw [hinvv x hxv]
      _ = x * (c * v) * x⁻¹ := by group
      _ = x * (v * c) * x⁻¹ := by rw [hcv]
      _ = (x * v) * c * x⁻¹ := by group
      _ = (v * x) * c * x⁻¹ := by rw [hxv]
      _ = v * (x * c * x⁻¹) := by group
  have hgv' : g⁻¹ * v = v * g⁻¹ := hinvv g hgv
  have hgC : g ∈ Subgroup.normalizer (C : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro c
    refine ⟨hconj g hgv c, fun h => ?_⟩
    have := hconj g⁻¹ hgv' _ h
    simpa [mul_assoc] using this
  have hgCc := mem_centralizer_of_odd_of_isCyclic hC2 hCc hgC hodd
  let A := Subgroup.zpowers g
  let Bv := Subgroup.zpowers v
  let α : A →* MulAut R := MulAut.conjNormal.comp A.subtype
  let β : Bv →* MulAut R := MulAut.conjNormal.comp Bv.subtype
  have hcomm : ∀ a b, α a * β b = β b * α a := by
    rintro ⟨a, i, rfl⟩ ⟨b, j, rfl⟩
    change MulAut.conjNormal (g ^ i) * MulAut.conjNormal (v ^ j) =
      MulAut.conjNormal (v ^ j) * MulAut.conjNormal (g ^ i)
    rw [← map_mul, ← map_mul, ((Commute.zpow_zpow (hgv : Commute g v)) i j).eq]
  have hfix : ∀ a r, (∀ b, β b r = r) → α a r = r := by
    rintro ⟨a, i, rfl⟩ r hr
    have hrC : (r : X) ∈ C := by
      refine ⟨r.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have h := congrArg Subtype.val (hr ⟨v, Subgroup.mem_zpowers v⟩)
      change v * r * v⁻¹ = r at h
      rw [mul_inv_eq_iff_eq_mul] at h
      exact h.symm
    have hgr : g * r = r * g := (Subgroup.mem_centralizer_iff.mp hgCc r hrC).symm
    apply Subtype.ext
    change g ^ i * r * (g ^ i)⁻¹ = r
    rw [((Commute.zpow_left (hgr : Commute g r)) i).eq, mul_inv_cancel_right]
  have hA : ¬ 2 ∣ Nat.card A := by
    rw [Nat.card_zpowers]
    exact hodd.not_two_dvd_nat
  have h := CFSG.GroupTheory.thompson_A_times_B hR2 hA hv2 α β hcomm hfix
    ⟨g, Subgroup.mem_zpowers g⟩
  refine Subgroup.mem_centralizer_iff.mpr fun r hr => ?_
  have h' := congrArg (fun φ : MulAut R => ((φ ⟨r, hr⟩ : R) : X)) h
  change g * r * g⁻¹ = r at h'
  rw [mul_inv_eq_iff_eq_mul] at h'
  exact h'.symm

namespace BaseConfig

variable {Y : Subgroup X} {e v : X}

theorem isPGroup_of_layer_eq_bot (hc : BaseConfig Y e) (hv : v * v = e)
    (hvn : (Subgroup.zpowers v).Normal) (hlayer : CFSG.layer X = ⊥) : IsPGroup 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar := CFSG.isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot X 2
    hc.oddCore_eq_bot hlayer
  change Subgroup.centralizer (CFSG.pCore 2 X : Set X) ≤ CFSG.pCore 2 X at hchar
  have hinv : ∀ a ∈ CFSG.Open.pCore 2 X, ∀ b ∈ CFSG.Open.pCore 2 X, orderOf a = 2 →
      orderOf b = 2 → a = b := fun a ha b hb ha2 hb2 =>
    (hc.eq_of_mem_twoCore ha ha2).trans (hc.eq_of_mem_twoCore hb hb2).symm
  intro x
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  refine ⟨k, ?_⟩
  have hyord : orderOf (x ^ 2 ^ k) = m := by
    rw [orderOf_pow_of_dvd (by positivity) (by rw [hkm]; exact Dvd.intro m rfl), hkm,
      Nat.mul_div_cancel_left _ (by positivity)]
  have hyR := hchar (mem_centralizer_of_odd_of_rank_one (TheoremC.twoCore_isPGroup X) hinv
    (hc.mem_twoCore_of_sq hv hvn) (hc.orderOf_eq_four hv) hvn (hyord ▸ hm))
  obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.mp (TheoremC.twoCore_isPGroup X) ⟨_, hyR⟩
  rw [Subgroup.orderOf_mk, hyord] at hj
  have hm1 : m = 1 := by
    rcases j with _ | j
    · rw [hj, pow_zero]
    · rw [hj] at hm
      exact absurd (Nat.even_pow.mpr ⟨even_two, j.succ_ne_zero⟩) (Nat.not_even_iff_odd.mpr hm)
  exact orderOf_eq_one_iff.mp (hyord.trans hm1)

theorem exists_component_of_sq (hc : BaseConfig Y e) (hv : v * v = e)
    (hvn : (Subgroup.zpowers v).Normal) : ∃ L : Subgroup X, CFSG.IsComponent L := by
  by_contra hno
  push Not at hno
  have hlayer : CFSG.layer X = ⊥ := by
    refine le_bot_iff.mp (sSup_le fun L hL => ?_)
    exact absurd hL (hno L)
  have hX := hc.isPGroup_of_layer_eq_bot hv hvn hlayer
  obtain ⟨P, hPY, -⟩ := hc.sylow
  have hP : (⊤ : Subgroup X) = P := P.is_maximal' (hX.to_subgroup ⊤) le_top
  exact hc.ne_top (top_le_iff.mp (hP ▸ hPY))

theorem exists_component_not_le_of_sq (hc : BaseConfig Y e) (hv : v * v = e)
    (hvn : (Subgroup.zpowers v).Normal) : ∃ L : Subgroup X, CFSG.IsComponent L ∧ ¬ L ≤ Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hall
  push Not at hall
  set N := CFSG.layer X ⊔ CFSG.Open.pCore 2 X with hN
  have : N.Normal := by
    have := layer_normal (X := X)
    have := TheoremC.twoCore_normal (X := X)
    infer_instance
  have hNY : N ≤ Y := sup_le (sSup_le fun L hL => hall L hL) hc.twoCore_le
  obtain ⟨P₀⟩ : Nonempty (Sylow 2 N) := inferInstance
  have hP₀Y : (P₀ : Subgroup N).map N.subtype ≤ Y := (Subgroup.map_subtype_le _).trans hNY
  have hNrank : CFSG.Open.pRank 2 N ≤ 1 := by
    by_contra hlt
    have h2 : 2 ≤ CFSG.Open.pRank 2 ((P₀ : Subgroup N).map N.subtype) := by
      rw [sylow_image_two_rank_eq]
      omega
    have hnorm := hc.normalizer_le _ hP₀Y h2
    have hfrat := Sylow.normalizer_sup_eq_top P₀
    exact hc.ne_top (top_le_iff.mp (hfrat ▸ sup_le hnorm hNY))
  obtain ⟨L, hL⟩ := hc.exists_component_of_sq hv hvn
  obtain ⟨P, -, -⟩ := hc.sylow
  have hRN : ((P : Subgroup X) ⊓ L) ⊔ Subgroup.zpowers v ≤ N := by
    have hLE : L ≤ CFSG.layer X := le_sSup hL
    refine sup_le (inf_le_right.trans (hLE.trans le_sup_left)) ?_
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_sup_right (hc.mem_twoCore_of_sq hv hvn)
  have h2 := hc.two_le_pRank_sup hv hvn P hL
  have hmono := CFSG.SectionRank.pRank_mono (p := 2) (by decide) hRN
  omega

theorem exists_oneComponent_of_sq (hc : BaseConfig Y e) (hv : v * v = e)
    (hvn : (Subgroup.zpowers v).Normal) (hall : ∀ L : Subgroup X, CFSG.IsComponent L → e ∈ L) :
    ∃ L : Subgroup X, OneComponent Y e v L := by
  obtain ⟨L, hL, hLY⟩ := hc.exists_component_not_le_of_sq hv hvn
  have hunique : ∀ L' : Subgroup X, CFSG.IsComponent L' → L' = L := fun L' hL' =>
    hc.component_unique hv hvn hL hLY hL'
  have hlayer := layer_eq_of_unique hL hunique
  have hnormal : L.Normal := hlayer ▸ layer_normal
  obtain ⟨hZc, hZO⟩ := hc.component_center_isCyclic hL
  exact ⟨L, hL, hunique, hlayer, hnormal, hall L hL, hLY, mem_centralizer_component hvn hL,
    fun k hk hk2 => hc.eq_of_mem_centralizer_of_not_le hLY hk hk2, hZc, hZO⟩

end BaseConfig

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
