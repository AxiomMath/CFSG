module

public import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionCover
public import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneQuaternionRecognition
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.G2SylIAAsm
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.G2SylIASD
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.G2SylIASL2
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2SylCore
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1Glue1

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec6.G2Syl
open scoped commutatorElement

namespace Std4r1

variable {G : Type} [Group G] [Finite G] {z : G} {S K F : Subgroup G}

theorem z_mem_zStar' (h : Std4r1 G z S K F) : z ∈ zStar K := by
  obtain ⟨t₀, ht₀C, ht₀z, ht₀n⟩ := h.thm2
  have hcl := h.classical.2 t₀ ht₀C ht₀z ht₀n
  have hb : CFSG.ABGLocalTools.IsSylowOf 2 (zpowers z) (zStar K) := by
    have := hcl.2.1
    rwa [h.rigidProduct_eq] at this
  obtain ⟨Q, hQ⟩ := hb
  have hz : z ∈ (Q : Subgroup ↥(zStar K)).map (zStar K).subtype := by
    rw [hQ]; exact mem_zpowers z
  obtain ⟨q, -, hq⟩ := hz
  rw [← hq]
  exact q.2

theorem z_mem_K' (h : Std4r1 G z S K F) : z ∈ K := h.z_mem_zStar'.1

theorem z_mem_P' (h : Std4r1 G z S K F) : z ∈ S ⊓ K := ⟨h.z_mem_S, h.z_mem_K'⟩

theorem z_mem_Q' (h : Std4r1 G z S K F) : z ∈ S ⊓ cSec K := ⟨h.z_mem_S, h.z_mem_zStar'.2⟩

theorem P_inv' (h : Std4r1 G z S K F) {x : G} (hx : x ∈ S ⊓ K) (hx2 : x * x = 1) :
    x = 1 ∨ x = z := by
  have hcomm : x * z = z * x := M.centralizer_comm (h.K_le_C hx.2)
  rcases rk1_of_pRank_one h.comp_pRank x hx.2 z h.z_mem_K' hx2 h.z_sq hcomm with h1 | h1 | h1
  · exact Or.inl h1
  · exact absurd h1 h.z_ne
  · exact Or.inr h1

theorem sylow_P (h : Std4r1 G z S K F) :
    CFSG.QuasithinUnique.IsSylowTwoOf (S ⊓ K) K := by
  have hS : CFSG.QuasithinUnique.IsSylowTwoOf S (centralizer ({z} : Set G)) :=
    ⟨h.syl_C.1, h.syl_C.2.1, h.syl_C.2.2⟩
  have hsub : (K.subgroupOf (centralizer ({z} : Set G))).IsSubnormal := by
    obtain ⟨K', -, hsubn, -⟩ := h.comp_isPCompIn.2
    exact hsubn
  exact CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_inf_of_subnormal hS h.K_le_C hsub

end Std4r1

theorem sylow_transfer {K : Type*} [Group K] [Finite K] {F : Type*} [Field F] [Finite F]
    (f : K →* Matrix.SpecialLinearGroup (Fin 2) F) (hf : Function.Surjective f)
    (P : Subgroup K) (hP : ∃ P' : Sylow 2 K, (P' : Subgroup K) = P)
    (hinj : ∀ p ∈ P, f p = 1 → p = 1) :
    ((2 : F) = 0 → ∀ p ∈ P, p * p = 1) ∧
    ((2 : F) ≠ 0 → Nat.card ↥P = 2 ^ ((Nat.card F ^ 2 - 1).factorization 2) ∧
      ∃ a ∈ P, ∃ b ∈ P, a * b ≠ b * a) := by
  obtain ⟨P', rfl⟩ := hP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T : Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) F) := Sylow.mapSurjective hf P' with hT
  have hTc : (T : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) = (P' : Subgroup K).map f :=
    Sylow.coe_mapSurjective hf P'
  refine ⟨fun h2 p hp => ?_, fun h2 => ⟨?_, ?_⟩⟩
  · have hfp : f p ∈ (T : Subgroup _) := by rw [hTc]; exact ⟨p, hp, rfl⟩
    obtain ⟨j, hj⟩ := T.isPGroup' ⟨f p, hfp⟩
    have hj' : (f p) ^ (2 ^ j) = 1 := by simpa using congrArg Subtype.val hj
    have := sl2_sq_eq_one_of_char_two h2 (f p) hj'
    apply hinj (p * p) ((P' : Subgroup K).mul_mem hp hp)
    rw [map_mul]; exact this
  · rw [← sl2_sylow_card h2 T, hTc]
    have hinj' : Function.Injective (f.comp (P' : Subgroup K).subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      rw [MonoidHom.mem_ker] at hx
      rw [Subgroup.mem_bot]
      exact Subtype.ext (hinj x x.2 hx)
    have hr : (f.comp (P' : Subgroup K).subtype).range = (P' : Subgroup K).map f := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hr]
    exact Nat.card_congr (MonoidHom.ofInjective hinj').toEquiv
  · obtain ⟨a, ha, b, hb, hab⟩ := sl2_sylow_noncomm h2 T
    rw [hTc] at ha hb
    obtain ⟨p, hp, rfl⟩ := ha
    obtain ⟨p', hp', rfl⟩ := hb
    exact ⟨p, hp, p', hp', fun h => hab (by rw [← map_mul, ← map_mul, h])⟩




theorem card_of_isQuaternionTwoGroup {Y : Type} [Group Y] {n : ℕ} (hY : IVK.IsQuaternionTwoGroup Y n) :
    Nat.card Y = 2 ^ n := by
  obtain ⟨hn, ⟨e⟩⟩ := hY
  have : NeZero (2 ^ (n - 2)) := ⟨by positivity⟩
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have : 2 ^ n = 4 * 2 ^ (n - 2) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [Nat.add_sub_cancel, pow_add]; ring
  rw [this]


section Main

open CFSG.GH74.GLS.Stage1.Thm3.Sec8 CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl


theorem ia_4_5_1 : IA_4_5_1 := by
  intro G _ _ z S K F h hQF hquatF y hyS hy2 hyR hSR hPsd hQsd hcard Fq _ _ ⟨e⟩
  classical
  obtain ⟨nQ, hnQ⟩ := hquatF
  obtain ⟨mP, hmP⟩ := hPsd
  obtain ⟨mQ, hmQ⟩ := hQsd
  have hP : Pz S z = S ⊓ K := h.Pz_eq
  have hQ : Qz S z = S ⊓ cSec K := h.Qz_eq
  have hR : Rz S z = (S ⊓ K) ⊔ (S ⊓ cSec K) := h.Rz_eq
  rw [← hQF, hQ] at hnQ
  rw [hP] at hmP hcard
  rw [hQ] at hmQ hcard
  rw [hR] at hyR hSR
  have hy2' : y * y = 1 := mul_self_eq_one_of_orderOf_eq_two hy2
  have hz1 : z ≠ 1 := h.z_ne
  have hz2 : z * z = 1 := h.z_sq
  have hzP : z ∈ S ⊓ K := h.z_mem_P'
  have hzQ : z ∈ S ⊓ cSec K := h.z_mem_Q'
  have hyP : y ∉ S ⊓ K := fun hy => hyR (mem_sup_left hy)
  have hyQ : y ∉ S ⊓ cSec K := fun hy => hyR (mem_sup_right hy)
  have hnormP : ∀ x ∈ S ⊓ K, y * x * y⁻¹ ∈ S ⊓ K := fun x hx => h.P_norm hyS hx
  have hnormQ : ∀ x ∈ S ⊓ cSec K, y * x * y⁻¹ ∈ S ⊓ cSec K := fun x hx => h.Q_norm hyS hx
  have hQcard : Nat.card ↥(S ⊓ cSec K) = 2 ^ nQ := card_of_isQuaternionTwoGroup hnQ
  have hQ8 : 8 ≤ 2 ^ nQ := by
    have h3 : 3 ≤ nQ := hnQ.1
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ nQ := Nat.pow_le_pow_right (by norm_num) h3
  set eSL := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 Fq with heSL
  set f : ↥K →* Matrix.SpecialLinearGroup (Fin 2) Fq :=
    (eSL.symm.toMonoidHom).comp ((e.toMonoidHom).comp (QuotientGroup.mk' (pPrimeCore 2 ↥K)))
    with hf
  have hfs : Function.Surjective f := by
    intro A
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (e.symm (eSL A))
    refine ⟨x, ?_⟩
    have : e (QuotientGroup.mk x) = eSL A := by rw [hx]; exact e.apply_symm_apply _
    change eSL.symm (e (QuotientGroup.mk x)) = A
    rw [this]; exact eSL.symm_apply_apply A
  have hinj : ∀ p ∈ (S ⊓ K).subgroupOf K, f p = 1 → p = 1 := by
    intro p hp hfp
    have h1 : e (QuotientGroup.mk p) = 1 := by
      have : eSL.symm (e (QuotientGroup.mk p)) = 1 := hfp
      exact (eSL.symm.map_eq_one_iff).1 this
    have h2 : (QuotientGroup.mk p : HatT K) = 1 := (e.map_eq_one_iff).1 h1
    have h3 : p ∈ pPrimeCore 2 ↥K := (QuotientGroup.eq_one_iff p).1 h2
    have h4 : (p : G) ∈ S ⊓ pPrimeCoreOf 2 K := ⟨(Subgroup.mem_subgroupOf.1 hp).1, ⟨p, h3, rfl⟩⟩
    rw [h.S_inf_O, Subgroup.mem_bot] at h4
    exact Subtype.ext h4
  have hsylP := h.sylow_P
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpgK : IsPGroup 2 ↥((S ⊓ K).subgroupOf K) :=
    hsylP.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hsylP.1).symm
  have hPsyl : ∃ P' : Sylow 2 ↥K, (P' : Subgroup ↥K) = (S ⊓ K).subgroupOf K :=
    ⟨hpgK.toSylow hsylP.2.2, rfl⟩
  have htr := sylow_transfer f hfs _ hPsyl hinj
  have hcardPK : Nat.card ↥((S ⊓ K).subgroupOf K) = Nat.card ↥(S ⊓ K) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsylP.1).toEquiv
  have hPQcard : Nat.card ↥(S ⊓ K) = 2 ^ nQ := by rw [hcard, hQcard]
  have h2 : (2 : Fq) ≠ 0 := by
    intro h20
    have hall := htr.1 h20
    have hle : (S ⊓ K) ≤ zpowers z := by
      intro x hx
      have hxK : x ∈ K := hx.2
      have h1 := hall ⟨x, hxK⟩ (Subgroup.mem_subgroupOf.2 hx)
      have hx2 : x * x = 1 := congrArg Subtype.val h1
      rcases h.P_inv' hx hx2 with h1 | h1
      · rw [h1]; exact one_mem _
      · rw [h1]; exact mem_zpowers z
    have h1 : Nat.card ↥(S ⊓ K) ≤ Nat.card ↥(zpowers z) := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, h.orderOf_z] at h1
    omega
  obtain ⟨hPcardK, hnoncomm⟩ := htr.2 h2
  have hPcard' : Nat.card ↥(S ⊓ K) = 2 ^ ((Nat.card Fq ^ 2 - 1).factorization 2) := by
    rw [← hcardPK]; exact hPcardK
  obtain ⟨a, ha, b, hb, hab⟩ := hnoncomm
  have hnonab : ∃ u v : ↥(S ⊓ K), u * v ≠ v * u := by
    refine ⟨⟨(a : G), (Subgroup.mem_subgroupOf.1 ha)⟩, ⟨(b : G), Subgroup.mem_subgroupOf.1 hb⟩,
      fun hc => hab ?_⟩
    apply Subtype.ext
    have := congrArg (fun x : ↥(S ⊓ K) => (x : G)) hc
    simpa using this
  have hrank : CFSG.DisconnectedInvolutionGraph.Helpers.NoCommutingDistinctInvolutions ↥(S ⊓ K) := by
    have hu : ∀ u : CFSG.DisconnectedInvolutionGraph.Helpers.Involution ↥(S ⊓ K),
        ((u.1 : ↥(S ⊓ K)) : G) = z := by
      intro u
      have ho : orderOf ((u.1 : ↥(S ⊓ K)) : G) = 2 := by rw [Subgroup.orderOf_coe]; exact u.2
      rcases h.P_inv' (u.1 : ↥(S ⊓ K)).2 (mul_self_eq_one_of_orderOf_eq_two ho) with h1 | h1
      · rw [h1, orderOf_one] at ho; omega
      · exact h1
    intro u v _
    exact Subtype.ext (Subtype.ext ((hu u).trans (hu v).symm))
  obtain ⟨ee, hee1, ⟨εQ⟩⟩ := CFSG.DisconnectedInvolutionGraph.Helpers.rank_one_two_nonabelian_quaternion
    hsylP.2.1 hrank hnonab
  have hPq : IVK.IsQuaternionTwoGroup ↥(S ⊓ K) (ee + 2) :=
    ⟨by omega, ⟨by rw [Nat.add_sub_cancel]; exact εQ.symm⟩⟩
  have hnPQ : ee + 2 = nQ := by
    have h1 : 2 ^ (ee + 2) = 2 ^ nQ := by rw [← card_of_isQuaternionTwoGroup hPq, hPQcard]
    exact Nat.pow_right_injective (le_refl 2) h1
  rw [hnPQ] at hPq
  obtain ⟨c₁, w₁, k₁, hc₁P, hw₁P, hPcl, hk₁, hc₁1, hc₁z, hw₁z, hw₁c, hyc₁, hyw₁, hZ₁⟩ :=
    sdq_data hy2' hyP hnormP hzP hz2 hz1 hPq hmP
  obtain ⟨c₂, w₂, k₂, hc₂Q, hw₂Q, hQcl, hk₂, hc₂1, hc₂z, hw₂z, hw₂c, hyc₂, hyw₂, hZ₂⟩ :=
    sdq_data hy2' hyQ hnormQ hzQ hz2 hz1 hnQ hmQ
  have hnn : 2 ≤ nQ - 1 := by have := hnQ.1; omega
  have hcomm : ∀ p ∈ S ⊓ K, ∀ q ∈ S ⊓ cSec K, p * q = q * p := fun p hp q hq => h.comm_PQ hp hq
  have hint : (S ⊓ K) ⊓ (S ⊓ cSec K) ≤ zpowers z := by
    rintro x ⟨hxP, hxQ⟩
    have hcen : ∀ p ∈ S ⊓ K, p * x = x * p := fun p hp => h.comm_PQ hp hxQ
    rcases hZ₁ x hxP hcen with h1 | h1
    · rw [h1]; exact one_mem _
    · rw [h1]; exact mem_zpowers z
  have hnn1 : nQ - 1 - 1 = nQ - 2 := by omega
  obtain ⟨A, a', t, y', hSC⟩ := CFSG.GH74.GLS.Stage1.Thm3.Sec6.G2Syl.ia_assemble hnn hy2' hyR hz1 hPcl hQcl
    hc₁1 (by rw [hnn1]; exact hc₁z) hw₁z hw₁c hyc₁ hyw₁ hk₁
    hc₂1 (by rw [hnn1]; exact hc₂z) hw₂z hw₂c hyc₂ hyw₂ hk₂ hcomm hint
  rw [← hSR] at hSC
  have := Fintype.ofFinite Fq
  have hch : ringChar Fq ≠ 2 := by
    intro hc
    apply h2
    have h1 := CharP.cast_eq_zero Fq (ringChar Fq)
    rw [hc] at h1
    simpa using h1
  obtain ⟨f', hp, hpf⟩ := FiniteField.card Fq (ringChar Fq)
  have hval : (((ringChar Fq) ^ (f' : ℕ)) ^ 2 - 1).factorization 2 = (nQ - 1) + 1 := by
    rw [← hpf, ← Nat.card_eq_fintype_card]
    have h1 : 2 ^ ((Nat.card Fq ^ 2 - 1).factorization 2) = 2 ^ nQ := by rw [← hPcard', hPQcard]
    have h2' := Nat.pow_right_injective (le_refl 2) h1
    rw [h2']; have := hnQ.1; omega
  obtain ⟨Gs, iG, fG, hL, S', hS'⟩ := g2_sylow_of_shapeConds hSC (ringChar Fq) f' hp hch f'.pos hval
  exact ⟨Gs, iG, fG, ringChar Fq, f', hp, hch, by rw [← hpf, ← Nat.card_eq_fintype_card], hL, S', hS'⟩

end Main

end CFSG.GH74.GLS.Stage1.Thm3.Sec6
