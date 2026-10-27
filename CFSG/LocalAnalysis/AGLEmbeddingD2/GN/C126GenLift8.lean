module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenLift6
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.AGLEmbeddingD2.GN

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.B6 Equiv
  CFSG.LieType.BorelTits

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {N : ℕ}

omit [Finite G] in
theorem mem_of_pow_three_of_two_element {K : Subgroup G} {q k y : G}
    (hq : q ∈ Subgroup.normalizer (K : Set G)) (hk : k ∈ K) (hy : y = q * k) {m : ℕ}
    (hqm : q ^ 2 ^ m = 1) (hy3 : y ^ 3 = 1) : y ∈ K := by
  set N : Subgroup G := Subgroup.normalizer (K : Set G) with hN
  have hkN : k ∈ N := Subgroup.le_normalizer hk
  have hyN : y ∈ N := hy ▸ N.mul_mem hq hkN
  have hnorm : (K.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).2 le_rfl
  let π := QuotientGroup.mk' (K.subgroupOf N)
  have h1 : π ⟨k, hkN⟩ = 1 := (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hk)
  have h2 : π ⟨y, hyN⟩ = π ⟨q, hq⟩ := by
    have : (⟨y, hyN⟩ : ↥N) = ⟨q, hq⟩ * ⟨k, hkN⟩ := Subtype.ext hy
    rw [this, map_mul, h1, mul_one]
  have h3 : (π ⟨y, hyN⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨y, hyN⟩ : ↥N) ^ 3 = 1 := Subtype.ext (by simpa using hy3)
    rw [this, map_one]
  have h4 : (π ⟨y, hyN⟩) ^ 2 ^ m = 1 := by
    rw [h2, ← map_pow]
    have : (⟨q, hq⟩ : ↥N) ^ 2 ^ m = 1 := Subtype.ext (by simpa using hqm)
    rw [this, map_one]
  exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 (eq_one_of_pow_three h3 h4))

section CV

variable {V : Subgroup G} (hV : IsElemAbelian 2 V)

omit [Finite G] in
theorem cv_pow {g : G} (hg : g ∈ Subgroup.normalizer (V : Set G)) :
    ∀ n : ℕ, cv hV (g ^ n) = (cv hV g) ^ n
  | 0 => by simp [cv_one]
  | n + 1 => by
    rw [pow_succ, cv_mul hV (Subgroup.pow_mem _ hg n) hg, cv_pow hg n, pow_succ]

end CV

omit [Finite G] in
theorem GenData.th_pow {H T V Y : Subgroup G} {hV : IsElemAbelian 2 V} (d : GenData N H T V Y hV)
    {φ : MulAut (IntMod V hV)} (hφ : φ ∈ d.L) : ∀ n : ℕ, d.th (φ ^ n) = (d.th φ) ^ n
  | 0 => by simp [d.th_one]
  | n + 1 => by
    rw [pow_succ, d.th_mul (d.L.pow_mem hφ n) hφ, GenData.th_pow d hφ n, pow_succ]

namespace SymLift

variable {H T M V Y : Subgroup G} {hV : IsElemAbelian 2 V} {s : GenSetting H T M V Y hV}
  {d : GenData N H T V Y hV}

namespace XData

variable {x : G} (hx : XData s d x)

include hx

theorem mem_Khat_of_pow_three
    (hRad : twoResidual H ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 H) {y : G}
    (hy : y ∈ A₁ s d) (hyK : y ∈ twoResidual H) (hy3 : y ^ 3 = 1) : y ∈ Khat s d x := by
  have hyH : y ∈ H := (mem_A₁.1 hy).1
  have hyL : cv hV y ∈ d.L := (mem_A₁.1 hy).2
  have hyN : y ∈ Subgroup.normalizer (V : Set G) := s.H_le_N hyH
  have hcube : (d.th (cv hV y)) ^ 3 = 1 := by
    rw [← d.th_pow hyL, ← cv_pow hV hyN, hy3, cv_one, d.th_one]
  have hsign : d.th (cv hV y) ∈ alternatingGroup (Fin N) := mem_alt_of_pow_three hcube
  obtain ⟨k, hk⟩ := hx.alpha_surj ⟨d.th (cv hV y), hsign⟩
  have hk' : d.th (cv hV (k : G)) = d.th (cv hV y) := by
    have := congrArg Subtype.val hk
    rwa [alpha_apply] at this
  have hkcv : cv hV (k : G) = cv hV y := d.th_inj (hx.cv_mem_L k.2) hyL hk'
  have hkN : (k : G) ∈ Subgroup.normalizer (V : Set G) := s.H_le_N (hx.Khat_le_H k.2)
  have hkinv : (k : G)⁻¹ ∈ Subgroup.normalizer (V : Set G) := Subgroup.inv_mem _ hkN
  have hq1 : y * (k : G)⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
    rw [← cv_eq_one_iff hV (Subgroup.mul_mem _ hyN hkinv), cv_mul hV hyN hkinv,
      cv_inv hV hkN, hkcv, mul_inv_cancel]
  have hq2 : y * (k : G)⁻¹ ∈ twoResidual H :=
    (twoResidual H).mul_mem hyK ((twoResidual H).inv_mem (hx.Khat_le_twoResidual k.2))
  have hqQ : y * (k : G)⁻¹ ∈ pCoreOf 2 H := hRad ⟨hq2, hq1⟩
  obtain ⟨m, hm⟩ := pCoreOf_isPGroup 2 H ⟨_, hqQ⟩
  refine mem_of_pow_three_of_two_element (K := Khat s d x)
    (A₁_le_normalizer_Khat s d x (Q_le_A₁ (s := s) (d := d) hqQ)) k.2 ?_
    (congrArg Subtype.val hm) hy3
  group

theorem Jt_conj_mem_Khat
    (hRad : twoResidual H ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 H) {t k : G}
    (ht : t ∈ Jt s) (hk : k ∈ Khat s d x) : t * k * t⁻¹ ∈ Khat s d x := by
  have hxK : x ∈ twoResidual H :=
    mem_O2_of_odd (s.Y_le hx.mem) (by rw [hx.ord]; decide)
  have hx3 : x ^ 3 = 1 := by rw [← hx.ord]; exact pow_orderOf_eq_one x
  have htH : t ∈ H := ht.1
  have hxt : t * x * t⁻¹ ∈ Khat s d x := by
    refine hx.mem_Khat_of_pow_three hRad (conj_mem_A₁ ht hx.x_mem_A₁) ?_ ?_
    · exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_twoResidual H htH) x).1 hxK
    · rw [conj_pow, hx3]; simp
  have hle : Khat s d x ≤ (Khat s d x).comap (MulAut.conj t).toMonoidHom := by
    refine conjClosure_le fun a ha z hz => ?_
    have hta : t * a * t⁻¹ ∈ A₁ s d := conj_mem_A₁ ht ha
    have hz' : z ∈ Subgroup.zpowers x := hz
    have htz : t * z * t⁻¹ ∈ Khat s d x := by
      have hzle : Subgroup.zpowers x ≤ (Khat s d x).comap (MulAut.conj t).toMonoidHom := by
        rw [Subgroup.zpowers_le]
        exact hxt
      exact hzle hz'
    have := (Subgroup.mem_normalizer_iff.1 (A₁_le_normalizer_Khat s d x hta) (t * z * t⁻¹)).1 htz
    show t * (a * z * a⁻¹) * t⁻¹ ∈ Khat s d x
    convert this using 1
    group
  exact hle hk

end XData

theorem thompsonJ_le_Jt (s : GenSetting H T M V Y hV) : thompsonJ T ≤ Jt s := by
  intro t ht
  refine ⟨s.hT.1 ((thompsonJ_le T) ht), ?_⟩
  exact (mem_autI_iff hV ((thompsonJ_le H).trans s.H_le_N)).2
    ⟨t, thompsonJ_le_of_sylow s.hT ht, rfl⟩

end SymLift

omit [Finite G] in
theorem blockU_le_blockQ_gen (K : Subgroup G) : blockU K ≤ blockQ K := by
  unfold blockU
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have h := (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 K hb) a⁻¹).1
    ((blockQ K).inv_mem ha)
  have e : ⁅a, b⁆ = a * (b * a⁻¹ * b⁻¹) := by rw [commutatorElement_def]; group
  rw [e]
  exact (blockQ K).mul_mem ha h

namespace SymLift

variable {H T M V Y : Subgroup G} {hV : IsElemAbelian 2 V} {s : GenSetting H T M V Y hV}
  {d : GenData N H T V Y hV}

namespace XData

variable {x : G} (hx : XData s d x)

include hx

omit [Finite G] in
theorem eq_top_of_isPGroup_quotient (N : Subgroup ↥(Khat s d x)) [N.Normal]
    (hN : IsPGroup 2 (↥(Khat s d x) ⧸ N)) : N = ⊤ := by
  have h3 : ∀ k : ↥(Khat s d x), k ^ 3 = 1 → k ∈ N := by
    intro k hk
    have h1 : (QuotientGroup.mk k : ↥(Khat s d x) ⧸ N) ^ 3 = 1 := by
      rw [← QuotientGroup.mk_pow, hk, QuotientGroup.mk_one]
    obtain ⟨m, hm⟩ := hN (QuotientGroup.mk k)
    exact (QuotientGroup.eq_one_iff k).1 (eq_one_of_pow_three h1 hm)
  have hK : Khat s d x ≤ N.map (Khat s d x).subtype := by
    refine conjClosure_le fun a ha z hz => ?_
    have hmem : a * z * a⁻¹ ∈ Khat s d x := mem_conjClosure ha hz
    refine ⟨⟨_, hmem⟩, h3 _ (Subtype.ext ?_), rfl⟩
    have hz3 : z ^ 3 = 1 :=
      orderOf_dvd_iff_pow_eq_one.1 (hx.ord ▸ orderOf_dvd_of_mem_zpowers hz)
    simp [conj_pow, hz3]
  rw [eq_top_iff]
  intro k _
  obtain ⟨n, hn, hnk⟩ := hK k.2
  have : n = k := Subtype.ext hnk
  rwa [← this]

variable (hY : IsShort2 Y) (hA3 : IsAltType Y 3)

include hY hA3

theorem clause3 : blockU (Khat s d x) ≤ blockQ (Khat s d x) ⊓
      Subgroup.centralizer (blockQ (Khat s d x) : Set G) ∧
    ∀ y ∈ blockU (Khat s d x), y ^ 2 = 1 := by
  have hU := hx.blockU_eq_Vc hY hA3
  refine ⟨le_inf (blockU_le_blockQ_gen _) ?_, fun y hy => ?_⟩
  · intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hq' : q ∈ pCoreOf 2 (Khat s d x) := hq
    have hqQ : q ∈ pCoreOf 2 H := (hx.pCoreOf_Khat ▸ hq').2
    have huV : u ∈ V := Vc_le_V (hU ▸ hu)
    exact (Subgroup.mem_centralizer_iff.1 (s.Q_le_C hqQ) u huV).symm
  · have hyV : y ∈ V := Vc_le_V (hU ▸ hy)
    exact hV.2 y hyV

theorem clause5 : blockZ (Khat s d x) < blockU (Khat s d x) ∧
    ∀ W : Subgroup G, blockZ (Khat s d x) ≤ W → W ≤ blockU (Khat s d x) →
      Khat s d x ≤ Subgroup.normalizer (W : Set G) →
      W = blockZ (Khat s d x) ∨ W = blockU (Khat s d x) := by
  refine ⟨?_, fun W _ hWU hN => ?_⟩
  · rw [hx.blockZ_eq_bot hY hA3]
    exact bot_lt_iff_ne_bot.2 hx.blockU_ne_bot
  · have hW : W ≤ Vc d := (hx.blockU_eq_Vc hY hA3) ▸ hWU
    rcases hx.irred_Vc hW hN with h | h
    · left; rw [h, hx.blockZ_eq_bot hY hA3]
    · right; rw [h, hx.blockU_eq_Vc hY hA3]

theorem isShort2 (hRad : twoResidual H ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 H) :
    IsShort2 (Khat s d x) := by
  refine ⟨fun N _ hN => hx.eq_top_of_isPGroup_quotient N hN, hx.charTwo_Khat,
    hx.clause3 hY hA3, Or.inl ?_, hx.clause5 hY hA3⟩
  have e : ↥(Khat s d x) ⧸ CFSG.pCore 2 ↥(Khat s d x) ≃* ↥(alternatingGroup (Fin N)) :=
    (QuotientGroup.quotientMulEquivOfEq (hx.alpha_ker hRad).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective hx.alpha hx.alpha_surj)
  exact isQuasisimple_of_alt d.hN e

theorem isBlock2 (hRad : twoResidual H ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 H) :
    IsBlock2 H (Khat s d x) :=
  ⟨hx.isShort2 hY hA3 hRad, hx.Khat_le_H, hx.Khat_subgroupOf_isSubnormal⟩

theorem isChiBlock (hRad : twoResidual H ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 H) :
    IsChiBlock H (Khat s d x) :=
  ⟨hx.isBlock2 hY hA3 hRad, Or.inr ⟨N, d.hodd, by have := d.hN; omega, hx.isAltType_N hY hA3 hRad⟩⟩

end XData

end SymLift

end CFSG.AGLEmbeddingD2.GN
