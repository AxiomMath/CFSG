module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76XFinal
public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4D13

public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.AschbacherTheorem3

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem mul_self_eq_one_of_mem_closure {X : Type*} [Group X] {s : Set X} {C : Subgroup X}
    (hsC : closure s ≤ C) (hC : IsMulCommutative C) (hs : ∀ x ∈ s, x ^ 2 = 1) {y : X}
    (hy : y ∈ closure s) : y * y = 1 := by
  induction hy using closure_induction with
  | mem x hx => rw [← pow_two]; exact hs x hx
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hxy : x * y = y * x := congrArg Subtype.val (hC.is_comm.comm ⟨x, hsC hx⟩ ⟨y, hsC hy⟩)
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [← hxy]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [ihx, ihy, one_mul]
  | inv x hx ih =>
    calc x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
      _ = 1 := by rw [ih, inv_one]

theorem exists_normal_le_of_stronglyClosed (hgold : CFSG.Goldschmidt.TopStatement)
    (hO : CFSG.Open.standardComponentOddCore G = ⊥) {S A : Subgroup G} (hS : IsSylowOf 2 S ⊤)
    (hAS : A ≤ S) (hAab : IsMulCommutative A)
    (hcl : ∀ a ∈ A, ∀ g : G, g⁻¹ * a * g ∈ S → g⁻¹ * a * g ∈ A) :
    ∃ Q : Subgroup G, Q ≤ A ∧ Q.Normal ∧ IsPGroup 2 Q ∧ ∀ a ∈ A, a * a ∈ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀, hP₀⟩ := Asc76X.exists_sylow_eq_of_isSylowOf_top hS
  have hAP₀ : A ≤ (P₀ : Subgroup G) := hP₀ ▸ hAS
  obtain ⟨-, hGb, -⟩ := CFSG.Goldschmidt.milestone_of_topStatement hgold G P₀ A hAP₀ hAab
    (by rw [hP₀]; exact hcl)
  set M := normalClosure (A : Set G) with hMdef
  have hMn : M.Normal := normalClosure_normal
  have hAM : A ≤ M := subset_normalClosure
  have hOM : CFSG.Open.goldschmidtOddCore ↥M = ⊥ := Asc76X.oddCore_eq_bot_of_normal' hO hMn
  set π := QuotientGroup.mk' (CFSG.Open.goldschmidtOddCore ↥M) with hπdef
  have hπinj : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hOM]
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  set Ab := (A.subgroupOf M).map π with hAbdef
  set Pc := CFSG.Open.pCore 2 (↥M ⧸ CFSG.Open.goldschmidtOddCore ↥M) with hPcdef
  set C := closure {t | t ∈ ((P₀ : Subgroup G).subgroupOf M).map π ⊓
      CFSG.Open.goldschmidtLayer (↥M ⧸ CFSG.Open.goldschmidtOddCore ↥M) ∧ t ^ 2 = 1}
    with hCdef
  have hAb : Ab = Pc ⊔ C := hGb
  have hPcAb : Pc ≤ Ab := hAb ▸ le_sup_left
  have hCAb : C ≤ Ab := hAb ▸ le_sup_right
  set Q := (Pc.comap π).map M.subtype with hQdef
  have hQA : Q ≤ A := by
    rintro _ ⟨m, hm, rfl⟩
    obtain ⟨a, ha, hae⟩ := hPcAb hm
    rw [← hπinj hae]
    exact ha
  have hQn : Q.Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨m, hm, rfl⟩ := hx
    have h1 : (Asc76X.conjQuot hMn g) (π m) ∈ Pc := by
      rw [hPcdef, ← Asc76X.openPCore_map_eq 2 (Asc76X.conjQuot hMn g)]
      exact ⟨π m, hm, rfl⟩
    rw [hπdef, Asc76X.conjQuot_mk] at h1
    exact ⟨⟨g * m * g⁻¹, hMn.conj_mem m m.2 g⟩, h1, rfl⟩
  have hQ2 : IsPGroup 2 Q := by
    rintro ⟨_, m, hm, rfl⟩
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCore_isPGroup
      (G := ↥M ⧸ CFSG.Open.goldschmidtOddCore ↥M) 2 ⟨π m, hm⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : π (m ^ 2 ^ k) = π 1 := by
      rw [map_pow, map_one]
      exact congrArg Subtype.val hk
    have h2 := congrArg Subtype.val (hπinj h1)
    simpa using h2
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hAab.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hAbab : IsMulCommutative Ab := by
    refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
    obtain ⟨a, ha, hax⟩ := x.2
    obtain ⟨b, hb, hby⟩ := y.2
    change (x : ↥M ⧸ CFSG.Open.goldschmidtOddCore ↥M) * y = y * x
    rw [← hax, ← hby, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hAcomm _ ha _ hb)
  refine ⟨Q, hQA, hQn, hQ2, fun a ha => ?_⟩
  have haM := hAM ha
  have h1 : π ⟨a, haM⟩ ∈ ((Pc ⊔ C : Subgroup _) : Set (↥M ⧸ CFSG.Open.goldschmidtOddCore ↥M)) := by
    rw [← hAb]
    exact mem_map_of_mem _ (show (⟨a, haM⟩ : M) ∈ A.subgroupOf M from ha)
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _
    (by rw [normalizer_eq_top_iff.mpr (CFSG.LieType.BorelTits.pCore_normal 2)]; exact le_top)]
    at h1
  obtain ⟨p, hp, c, hc, hpc⟩ := h1
  have hcc : c * c = 1 :=
    mul_self_eq_one_of_mem_closure hCAb hAbab (fun x hx => hx.2) hc
  obtain ⟨m₀, rfl⟩ := hπsurj p
  obtain ⟨c₀, rfl⟩ := hπsurj c
  have hm₀Q : (m₀ : G) ∈ Q := ⟨m₀, hp, rfl⟩
  have hac : (⟨a, haM⟩ : M) = m₀ * c₀ := hπinj (by rw [map_mul]; exact hpc.symm)
  have hc₀c₀ : c₀ * c₀ = 1 := hπinj (by rw [map_mul, map_one]; exact hcc)
  have hae : a = (m₀ : G) * c₀ := congrArg Subtype.val hac
  have hm₀A : (m₀ : G) ∈ A := hQA hm₀Q
  have hc₀A : (c₀ : G) ∈ A := by
    have : (c₀ : G) = (m₀ : G)⁻¹ * a := by rw [hae]; group
    rw [this]
    exact mul_mem (inv_mem hm₀A) ha
  have hcomm : (c₀ : G) * m₀ = m₀ * c₀ := hAcomm _ hc₀A _ hm₀A
  have hc₀c₀' : (c₀ : G) * c₀ = 1 := by
    have := congrArg Subtype.val hc₀c₀
    simpa using this
  have e : a * a = (m₀ : G) * m₀ := by
    calc a * a = (m₀ : G) * (c₀ * m₀) * c₀ := by rw [hae]; group
      _ = (m₀ : G) * (m₀ * c₀) * c₀ := by rw [hcomm]
      _ = (m₀ : G) * m₀ * (c₀ * c₀) := by group
      _ = (m₀ : G) * m₀ := by rw [hc₀c₀', mul_one]
  rw [e]
  exact mul_mem hm₀Q hm₀Q

theorem MinCounter.sec4W_normal_of_stronglyClosed (hgold : CFSG.Goldschmidt.TopStatement)
    {S : Subgroup G} (hM : MinCounter Ω S)
    (hcl : ∀ w ∈ sec4W Ω S, ∀ g : G, g⁻¹ * w * g ∈ S → g⁻¹ * w * g ∈ sec4W Ω S) :
    (sec4W Ω S).Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ := hM.assumption
  have hS := hM.sylow
  set W := sec4W Ω S with hWdef
  obtain ⟨Q, hQW, hQn, hQ2, hsq⟩ := exists_normal_le_of_stronglyClosed hgold hΩ.oddCore hS
    (sec4W_le S) (isMulCommutative_sec4W hΩ hS.isPGroup) hcl
  have hrotQ : ∀ L ∈ Ω, ∀ T V : Subgroup G, IsSylowOf 2 T L → IsDihedralRot V T →
      ∀ v ∈ V, v * v ∈ Q := by
    intro L hL T V hT hV v hv
    obtain ⟨S₁, hS₁, hTS₁⟩ := exists_isSylowOf_le hT.isPGroup (le_top : T ≤ ⊤)
    obtain ⟨k, -, hk⟩ := L26.IsSylowOf.exists_conj_mem hS hS₁
    have hVk : AschbacherTightEmbedding.rightConjugate V k ≤ S := by
      intro y hy
      rw [mem_rightConjugate_iff] at hy
      have h1 := (hk _).mp (hTS₁ (hV.le hy))
      have e : k⁻¹ * (k * y * k⁻¹) * k = y := by group
      rwa [e] at h1
    have hVW : AschbacherTightEmbedding.rightConjugate V k ≤ W :=
      le_sec4W hVk ((isRot_of hL hT hV).rightConjugate hΩ k)
    have h1 := hsq _ (hVW (conj_mem_rightConjugate hv k))
    have h2 := hQn.conj_mem _ h1 k
    have e : k * (k⁻¹ * v * k * (k⁻¹ * v * k)) * k⁻¹ = v * v := by group
    rwa [e] at h2
  have hZQ : ∀ L ∈ Ω, ∀ T V : Subgroup G, IsSylowOf 2 T L → IsDihedralRot V T →
      ∀ x ∈ V, x * x = 1 → x ∈ Q := by
    intro L hL T V hT hV x hx hxx
    obtain ⟨v, hv, rfl⟩ := hV.exists_sq_of_mul_self hx hxx
    exact hrotQ L hL T V hT hV v hv
  have hQO : ∀ q ∈ Q, q ∈ (CFSG.pCore 2 (G ⧸ CFSG.Assembly.oddCore G)).comap
      (QuotientGroup.mk' (CFSG.Assembly.oddCore G)) := by
    intro q hq
    have hn : (Q.map (QuotientGroup.mk' (CFSG.Assembly.oddCore G))).Normal :=
      hQn.map _ (QuotientGroup.mk'_surjective _)
    exact le_sSup (show _ ∈ {K : Subgroup (G ⧸ CFSG.Assembly.oddCore G) | K.Normal ∧
      IsPGroup 2 K} from ⟨hn, hQ2.map _⟩) (mem_map_of_mem _ hq)
  have hOK : ∀ K ∈ Ω, oddCoreIn K = ⊥ := by
    intro K hK
    obtain ⟨R, hR⟩ := exists_isSylowOf 2 K
    obtain ⟨U, hU⟩ := Assumption41.exists_rot hΩ hK hR
    obtain ⟨z, hzU, hz1, hzz, -, -⟩ := hU.exists_involution
    have hzQ := hZQ K hK R U hR hU z hzU hzz
    have hzK : z ∈ K := hR.le (hU.le hzU)
    have hbot : oddCoreIn K ⊓ Q = ⊥ :=
      eq_bot_of_isPGroup_of_odd (hQ2.to_le inf_le_right)
        ((odd_card_oddCoreIn K).of_dvd_nat (card_dvd_of_le inf_le_left))
    have hcent : ∀ o ∈ oddCoreIn K, o * z = z * o := by
      intro o ho
      have h1 : o * z * o⁻¹ * z⁻¹ ∈ oddCoreIn K ⊓ Q := by
        refine mem_inf.mpr ⟨?_, mul_mem (hQn.conj_mem z hzQ o) (inv_mem hzQ)⟩
        have h2 : z * o⁻¹ * z⁻¹ ∈ oddCoreIn K :=
          (mem_normalizer_iff.mp (le_normalizer_oddCoreIn K hzK) _).mp (inv_mem ho)
        have e : o * z * o⁻¹ * z⁻¹ = o * (z * o⁻¹ * z⁻¹) := by group
        rw [e]
        exact mul_mem ho h2
      rw [hbot, mem_bot] at h1
      calc o * z = o * z * o⁻¹ * z⁻¹ * (z * o) := by group
        _ = z * o := by rw [h1, one_mul]
    have hle1 : oddCoreIn K ≤ normalizer ((zpowers z : Subgroup G) : Set G) := fun o ho =>
      mem_normalizer_of_forall_mul_comm fun x hx => by
        obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
        exact ((Commute.zpow_right (hcent o ho) n) :)
    have hle2 : normalizer ((zpowers z : Subgroup G) : Set G) ≤
        normalizer ((oddCoreIn K : Subgroup G) : Set G) := by
      intro g hg
      have h1 : g * z * g⁻¹ ∈ zpowers z := (mem_normalizer_iff.mp hg z).mp (mem_zpowers z)
      have hgz : g ∈ centralizer ({z} : Set G) := by
        rw [mem_centralizer_singleton_iff]
        have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hzz) hz1
        have h2 : g * z * g⁻¹ = z := by
          have hmem : g * z * g⁻¹ ∈ ({1, z} : Set G) := by
            obtain ⟨n, hn⟩ := mem_zpowers_iff.mp h1
            rw [← hn]
            rcases Int.emod_two_eq_zero_or_one n with h | h
            · left
              rw [← zpow_mod_orderOf, hz2]
              norm_num [h]
            · right
              rw [← zpow_mod_orderOf, hz2]
              norm_num [h]
          rcases hmem with h | h
          · exfalso
            apply hz1
            have h' : g * z * g⁻¹ = 1 := h
            calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
              _ = 1 := by rw [h']; group
          · exact h
        calc g * z = g * z * g⁻¹ * g := by group
          _ = z * g := by rw [h2]
      exact normalizer_le_normalizer_oddCoreIn K
        (Sec4.centralizer_le_normalizer (Assumption41.tightlyEmbedded hΩ hK) hzK hz1 hzz hgz)
    have hle3 := le_oddCoreIn_of_le_normalizer hle1 hle2 (odd_card_oddCoreIn K)
    have hzP : IsPGroup 2 (zpowers z) :=
      isPGroup_zpowers_of_pow_eq_one (n := 1) (by rw [pow_one, pow_two]; exact hzz)
    have hle4 := L26.lemma29 hzP ((zpowers_le).mpr (hQO z hzQ))
    have h2 : CFSG.Assembly.oddCore G = ⊥ := hΩ.oddCore
    rw [h2] at hle4
    exact le_bot_iff.mp (hle3.trans hle4)
  apply sec4W_normal_of_rot_le hΩ
  intro J hJ T U hT hU
  have hJT : J ≤ T := by
    intro k hk
    obtain ⟨o, ho, r, hr, rfl⟩ := hM.twoNil J hJ T hT k hk
    rw [hOK J hJ, mem_bot] at ho
    rw [ho, one_mul]
    exact hr
  obtain ⟨x, hxU, hx1, hxx, -, -⟩ := hU.exists_involution
  obtain ⟨T', V', hT', hV', hxV', hT'W, hV'W⟩ := exists_isSylowOf_le_normalizer_of_mem hΩ hS hJ
    hT hU hxU hx1 hxx (hQW (hZQ J hJ T U hT hU x hxU hxx))
  have hTT' : T = T' := hT'.eq_of_le (hT'.le.trans hJT) hT.le hT.isPGroup
  rw [← hTT'] at hV'
  have hUV' : U = V' := hV'.eq_of_isCyclic hU.le hU.isCyclic hU.relIndex_eq
  rw [hUV']
  exact hV'W.trans (sec4W_le S)

theorem MinCounter.not_stronglyClosed (hgold : CFSG.Goldschmidt.TopStatement) {S : Subgroup G}
    (hM : MinCounter Ω S) :
    ¬ ∀ w ∈ sec4W Ω S, ∀ g : G, g⁻¹ * w * g ∈ S → g⁻¹ * w * g ∈ sec4W Ω S := fun hcl =>
  hM.not_normal (hM.sec4W_normal_of_stronglyClosed hgold hcl)

end CFSG.ComponentClassification.Asc76.Sec4
