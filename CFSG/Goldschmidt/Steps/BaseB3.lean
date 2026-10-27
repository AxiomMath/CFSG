module

public import CFSG.Goldschmidt.StatementsH
import CFSG.Goldschmidt.Steps.ZStarLemma
import CFSG.Goldschmidt.Steps.AbelSyl
import CFSG.Goldschmidt.Steps.Components
import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderExtensionData
public import CFSG.Goldschmidt.Statements

public section

namespace CFSG.Goldschmidt

open CFSG.Open
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter sylowCenter_le)
open CFSG.ComponentClassification.AschbacherToolkit.BenderExt
  (benderData_of_isBenderGroup extData_of_benderData)

section Omega

variable {G : Type*} [Group G]

private theorem omega1_le (T : Subgroup G) : Omega1 T ≤ T :=
  (Subgroup.closure_le T).mpr fun _ ht => ht.1

private theorem mem_omega1 {T : Subgroup G} {t : G} (ht : t ∈ T) (ht2 : t ^ 2 = 1) :
    t ∈ Omega1 T :=
  Subgroup.mem_closure_of_mem ⟨ht, ht2⟩

private theorem omega1_map {H : Type*} [Group H] {f : G →* H} (hf : Function.Injective f)
    (T : Subgroup G) : (Omega1 T).map f = Omega1 (T.map f) := by
  unfold Omega1
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨t, ⟨ht, ht2⟩, rfl⟩
    exact ⟨⟨t, ht, rfl⟩, by rw [← map_pow, ht2, map_one]⟩
  · rintro ⟨⟨t, ht, rfl⟩, h2⟩
    exact ⟨t, ⟨ht, hf (by rw [map_pow, h2, map_one])⟩, rfl⟩

private theorem omega1_subgroupOf {K T : Subgroup G} (hT : T ≤ K) :
    Omega1 (T.subgroupOf K) = (Omega1 T).subgroupOf K := by
  apply Subgroup.map_injective K.subtype_injective
  rw [omega1_map K.subtype_injective, Subgroup.subgroupOf_map_subtype,
    Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hT,
    inf_eq_left.mpr ((omega1_le T).trans hT)]

private theorem isMulCommutative_subgroupOf_iff {K H : Subgroup G} (hHK : H ≤ K) :
    IsMulCommutative (H.subgroupOf K) ↔ IsMulCommutative H := by
  constructor
  · intro h
    refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
    have hxy := h.is_comm.comm ⟨⟨x, hHK x.2⟩, x.2⟩ ⟨⟨y, hHK y.2⟩, y.2⟩
    exact congrArg (fun z : H.subgroupOf K => ((z : K) : G)) hxy
  · intro h
    refine ⟨⟨fun x y => ?_⟩⟩
    have hxy := h.is_comm.comm ⟨((x : K) : G), x.2⟩ ⟨((y : K) : G), y.2⟩
    have hxy' : ((x : K) : G) * ((y : K) : G) = ((y : K) : G) * ((x : K) : G) :=
      congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext hxy')

end Omega

section Simple

private theorem goldschmidtSimpleType_congr {L L' : Type} [Group L] [Group L'] (e : L ≃* L')
    (h : goldschmidtSimpleType L') : goldschmidtSimpleType L := by
  unfold goldschmidtSimpleType at h ⊢
  rcases h with ⟨f, hf, ⟨e'⟩⟩ | ⟨n, hn, ⟨e'⟩⟩ | ⟨f, hf, ⟨e'⟩⟩ |
      ⟨p, f, hp, hodd, hf, h5, h8, ⟨e'⟩⟩ | ⟨k, hk, hcard⟩ | ⟨⟨e'⟩⟩
  · exact Or.inl ⟨f, hf, ⟨e.trans e'⟩⟩
  · exact Or.inr (Or.inl ⟨n, hn, ⟨e.trans e'⟩⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨f, hf, ⟨e.trans e'⟩⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, f, hp, hodd, hf, h5, h8, ⟨e.trans e'⟩⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨k, hk, (Nat.card_congr e.toEquiv).trans hcard⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e.trans e'⟩))))

private theorem simple_facts (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) :
    goldschmidtOddCore G = ⊥ ∧ CFSG.Open.pCore 2 G = ⊥ ∧ goldschmidtLayer G = ⊤ ∧
      (∀ K : Subgroup G, IsComponentOf K ⊤ → K = ⊤) ∧ Subgroup.center G = ⊥ := by
  have hZ : Subgroup.center G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := hnab
      have ha : a ∈ Subgroup.center G := by rw [h]; exact Subgroup.mem_top a
      exact absurd (Subgroup.mem_center_iff.mp ha b).symm hab
  have hsimp : IsSimpleGroup (⊤ : Subgroup G) := Subgroup.topEquiv.isSimpleGroup
  have hnab' : ∃ a b : (⊤ : Subgroup G), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨⟨a, Subgroup.mem_top a⟩, ⟨b, Subgroup.mem_top b⟩,
      fun h => hab (congrArg Subtype.val h)⟩
  have hC : Subgroup.centralizer ((⊤ : Subgroup G) : Set G) = ⊥ := by
    rw [Subgroup.coe_top, Subgroup.centralizer_univ, hZ]
  obtain ⟨hO, hO2, hE, hcomp⟩ := N8g G ⊤ inferInstance hsimp hnab' hC
  exact ⟨hO, hO2, hE, hcomp, hZ⟩

theorem simpleConcl : S_simpleConcl := by
  intro G _ _ _ hnab S A
  obtain ⟨-, hO2, hE, hcomp, hZ⟩ := simple_facts G hnab
  have htop : IsComponentOf (⊤ : Subgroup G) ⊤ := by
    by_contra hnot
    have hbot : goldschmidtLayer G = ⊥ := by
      refine sSup_eq_bot.mpr fun K hK => ?_
      have hK' : IsComponentOf K ⊤ := hK
      obtain rfl := hcomp K hK'
      exact absurd hK' hnot
    rw [hE] at hbot
    exact top_ne_bot hbot
  have hZtop : Subgroup.center (⊤ : Subgroup G) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxG : (x : G) ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨g, Subgroup.mem_top g⟩)
    rw [hZ, Subgroup.mem_bot] at hxG
    exact (Subgroup.mem_bot).mpr (Subtype.ext hxG)
  let e : ((⊤ : Subgroup G) ⧸ Subgroup.center (⊤ : Subgroup G)) ≃* G :=
    (QuotientGroup.quotientMulEquivOfEq hZtop).trans
      (QuotientGroup.quotientBot.trans Subgroup.topEquiv)
  have htype : goldschmidtSimpleType ((⊤ : Subgroup G) ⧸ Subgroup.center (⊤ : Subgroup G)) ↔
      goldschmidtSimpleType G :=
    ⟨goldschmidtSimpleType_congr e.symm, goldschmidtSimpleType_congr e⟩
  have hgen : CFSG.Open.pCore 2 G ⊔
      Subgroup.closure {t | t ∈ (S : Subgroup G) ⊓ goldschmidtLayer G ∧ t ^ 2 = 1} =
      Omega1 (S : Subgroup G) := by
    rw [hO2, hE, bot_sup_eq, inf_top_eq]
    rfl
  unfold CoreConclusion
  rw [hgen, hO2, hE, bot_sup_eq]
  constructor
  · rintro ⟨-, hA, hK⟩
    exact ⟨htype.mp (hK ⊤ htop), hA⟩
  · rintro ⟨hG, hA⟩
    refine ⟨rfl, hA, fun K hK => ?_⟩
    obtain rfl := hcomp K hK
    exact htype.mpr hG

end Simple

theorem B3setup : S_B3setup := by
  intro G _ _ S A hA hIH K hKn hKs hKnab hKA hCK hAK
  obtain ⟨hOK, -, -, -, -⟩ := simple_facts K hKnab
  have hA0 : A ⊓ K ≠ ⊥ := by
    intro h0
    have hcomm : ⁅A, K⁆ = ⊥ := N6 G S A K hA.le hA.comm hA.closed
      (by rw [Subgroup.normalizer_eq_top K]; exact le_top) hOK h0
    have hAC := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    rw [hCK] at hAC
    exact hAK (hAC.trans bot_le)
  obtain ⟨T, hT⟩ := CFSG.Glauberman.sylow_inf_normal S (N := K)
  have hA'T : A.subgroupOf K ≤ (T : Subgroup K) := by
    intro x hx
    rw [hT, Subgroup.mem_subgroupOf]
    exact ⟨hA.le (Subgroup.mem_subgroupOf.mp hx), x.2⟩
  have hA'cl : fusionStronglyClosed ((A.subgroupOf K : Subgroup K) : Set K) (T : Subgroup K) := by
    intro a ha g hg
    rw [hT, Subgroup.mem_subgroupOf] at hg
    have ha' : (a : G) ∈ A := Subgroup.mem_subgroupOf.mp ha
    have h := hA.closed (a : G) ha' (g : G) hg.1
    show g⁻¹ * a * g ∈ A.subgroupOf K
    rw [Subgroup.mem_subgroupOf]
    exact h
  have hA'gen : Subgroup.normalClosure ((A.subgroupOf K : Subgroup K) : Set K) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.normalClosure ((A.subgroupOf K : Subgroup K) : Set K)) with h | h
    · refine absurd ?_ hA0
      have hle : A.subgroupOf K ≤ ⊥ := by rw [← h]; exact Subgroup.le_normalClosure
      rw [← Subgroup.subgroupOf_map_subtype, le_bot_iff.mp hle, Subgroup.map_bot]
    · exact h
  have hcard : Nat.card K < Nat.card G := by
    obtain ⟨a, -, haK⟩ := IsConcreteLE.not_le_iff_exists.mp hAK
    exact Finite.card_subtype_lt haK
  obtain ⟨htype, hAeq⟩ := (simpleConcl K hKnab T (A.subgroupOf K)).mp
    (hIH K hcard T (A.subgroupOf K) hA'T (isMulCommutative_subgroupOf hA.comm K) hA'cl hA'gen hOK)
  refine ⟨hA0, htype, ?_⟩
  rw [hT, omega1_subgroupOf inf_le_right, Subgroup.subgroupOf_inj,
    inf_eq_left.mpr ((omega1_le ((S : Subgroup G) ⊓ K)).trans inf_le_right)] at hAeq
  exact hAeq

theorem N24_of (h11a : S_N11a) : S_N24 := by
  intro G _ _ S A hA K hKn hKs hKnab hKA hCK hAK htype hA0 hTab
  obtain ⟨T, hT⟩ := CFSG.Glauberman.sylow_inf_normal S (N := K)
  have hmemT : ∀ x : K, x ∈ (T : Subgroup K) ↔ (x : G) ∈ (S : Subgroup G) ⊓ K := fun x => by
    rw [hT, Subgroup.mem_subgroupOf]
  have hTab' : IsMulCommutative (T : Subgroup K) := by
    rw [hT]
    exact (isMulCommutative_subgroupOf_iff inf_le_right).mpr hTab
  have hΩab : IsMulCommutative (Omega1 (T : Subgroup K)) :=
    isMulCommutative_anti (omega1_le (T : Subgroup K))
  have hel := (h11a K htype T hΩab).1 hTab'
  have hSKA : (S : Subgroup G) ⊓ K ≤ A := by
    intro t ht
    have ht2 : t ^ 2 = 1 := by
      have h := congrArg Subtype.val (hel ⟨t, ht.2⟩ ((hmemT _).mpr ht))
      simpa using h
    have hΩ := mem_omega1 ht ht2
    rw [← hA0] at hΩ
    exact hΩ.1
  have hdec : ∀ g : G, ∃ k ∈ K, ∃ a ∈ A, k * a = g := fun g =>
    Subgroup.mem_sup_of_normal_left.mp (by rw [hKA]; exact Subgroup.mem_top g)
  have hSA : (S : Subgroup G) ≤ A := by
    intro s hs
    obtain ⟨k, hk, a, ha, rfl⟩ := hdec s
    have hkS : k ∈ (S : Subgroup G) := by
      have h := (S : Subgroup G).mul_mem hs ((S : Subgroup G).inv_mem (hA.le ha))
      rwa [mul_inv_cancel_right] at h
    exact A.mul_mem (hSKA ⟨hkS, hk⟩) ha
  have hSab : IsMulCommutative (S : Subgroup G) := by
    have := hA.comm
    exact isMulCommutative_anti hSA
  obtain ⟨H, -, -, -, hfocal, -, hdsup, hcent⟩ := N7 G S hSab
  have hG'K : commutator G ≤ K := by
    rw [← Subgroup.Normal.quotient_commutative_iff_commutator_le]
    refine ⟨⟨fun x y => ?_⟩⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective K x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective K y
    obtain ⟨k, hk, a, ha, rfl⟩ := hdec x
    obtain ⟨l, hl, b, hb, rfl⟩ := hdec y
    have hk1 : QuotientGroup.mk' K k = 1 := (QuotientGroup.eq_one_iff k).mpr hk
    have hl1 : QuotientGroup.mk' K l = 1 := (QuotientGroup.eq_one_iff l).mpr hl
    have hab : a * b = b * a := congrArg Subtype.val (hA.comm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    rw [map_mul, map_mul, hk1, hl1, one_mul, one_mul, ← map_mul, ← map_mul, hab]
  have hne : (S : Subgroup G) ⊓ Subgroup.centralizer (H : Set G) ≠ ⊥ := by
    intro h
    rw [h, bot_sup_eq] at hdsup
    apply hAK
    calc A ≤ (S : Subgroup G) := hA.le
      _ = ⁅(S : Subgroup G), H⁆ := hdsup.symm
      _ = (S : Subgroup G) ⊓ commutator G := hfocal.symm
      _ ≤ K := inf_le_right.trans hG'K
  have hC2 : IsPGroup 2 ((S : Subgroup G) ⊓ Subgroup.centralizer (H : Set G) : Subgroup G) :=
    S.isPGroup'.to_le inf_le_left
  have hdvd : 2 ∣ Nat.card ((S : Subgroup G) ⊓ Subgroup.centralizer (H : Set G) : Subgroup G) :=
    hC2.card_eq_or_dvd.resolve_left fun h => hne (Subgroup.card_eq_one.mp h)
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hc2 : (c : G) ^ 2 = 1 := by
    have h := pow_orderOf_eq_one c
    rw [hc] at h
    simpa using congrArg Subtype.val h
  have hcZ := hcent hA.oddCore c c.2 hc2
  have hcK : (c : G) ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun k _ => Subgroup.mem_center_iff.mp hcZ k
  rw [hCK, Subgroup.mem_bot] at hcK
  have hc1 : c = 1 := Subtype.ext hcK
  rw [hc1, orderOf_one] at hc
  exact absurd hc (by norm_num)

theorem N25_of (h11a : S_N11a) : S_N25 := by
  intro G _ _ S A hA K hKn hKs hKnab hKA hCK hAK htype hA0 hTnab
  obtain ⟨T, hT⟩ := CFSG.Glauberman.sylow_inf_normal S (N := K)
  have hΩ : Omega1 (T : Subgroup K) = A.subgroupOf K := by
    rw [hT, omega1_subgroupOf inf_le_right, ← hA0, Subgroup.inf_subgroupOf_right]
  have hΩab : IsMulCommutative (Omega1 (T : Subgroup K)) := by
    rw [hΩ]
    exact isMulCommutative_subgroupOf hA.comm K
  have hTnab' : ¬ IsMulCommutative (T : Subgroup K) := by
    rw [hT]
    exact fun h => hTnab ((isMulCommutative_subgroupOf_iff inf_le_right).mp h)
  have hBender : fusionIsBenderGroup K := by
    rcases (h11a K htype T hΩab).2 hTnab' with ⟨n, hn, he⟩ | ⟨f, hf, he⟩
    · exact Or.inr (Or.inr ⟨n, hn, he⟩)
    · exact Or.inr (Or.inl ⟨f, hf, he⟩)
  have hKS : K ⊔ (S : Subgroup G) = ⊤ := by
    rw [eq_top_iff, ← hKA]
    exact sup_le_sup_left hA.le K
  have hD := extData_of_benderData K (benderData_of_isBenderGroup hBender) S hKS
  have hΩZ : A ⊓ K = sylowCenter ((S : Subgroup G) ⊓ K) := by
    rw [hA0]
    apply le_antisymm
    · exact (Subgroup.closure_le _).mpr fun t ht => hD.omega_one t ht.1 ht.2
    · intro z hz
      exact mem_omega1 (sylowCenter_le _ hz) (hD.sq_center z hz)
  obtain ⟨a, haA, haK⟩ := IsConcreteLE.not_le_iff_exists.mp hAK
  have hcomm : ∀ z ∈ sylowCenter ((S : Subgroup G) ⊓ K), a * z = z * a := by
    intro z hz
    rw [← hΩZ] at hz
    exact congrArg Subtype.val (hA.comm.is_comm.comm ⟨a, haA⟩ ⟨z, hz.1⟩)
  have hnot : a ∉ (S : Subgroup G) ⊓ K ⊔ Subgroup.centralizer (K : Set G) := by
    rw [hCK, sup_bot_eq]
    exact fun h => haK h.2
  obtain ⟨-, -, t, ht, htZ⟩ := hD.aut a (hA.le haA) hcomm hnot
  apply htZ
  rw [← hΩZ, Subgroup.mem_inf]
  refine ⟨?_, K.mul_mem (K.inv_mem ht.2) (hKn.conj_mem t ht.2 a)⟩
  have h1 : t⁻¹ * a * t ∈ A := conj_mem_of_stronglyClosed hA.le hA.closed ht.1 haA
  have h2 : t⁻¹ * (a * t * a⁻¹) = t⁻¹ * a * t * a⁻¹ := by group
  rw [h2]
  exact A.mul_mem h1 (A.inv_mem haA)

end CFSG.Goldschmidt
