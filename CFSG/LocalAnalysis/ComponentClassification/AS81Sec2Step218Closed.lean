module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step218Odd

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.GoldschmidtFour

namespace Sec2

variable {G : Type} [Group G] [Finite G]

theorem exists_relIndex_eq_two_pow {S D : Subgroup G} (hDN : D ≤ normalizer (S : Set G))
    (hsq : ∀ a ∈ D, a * a ∈ S) : ∃ n : ℕ, (D ⊓ S).relIndex D = 2 ^ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : ((D ⊓ S).subgroupOf D).Normal := ⟨fun n hn d => by
    rw [mem_subgroupOf] at hn ⊢
    refine ⟨D.mul_mem (D.mul_mem d.2 hn.1) (D.inv_mem d.2), ?_⟩
    exact (mem_normalizer_iff.mp (hDN d.2) _).mp hn.2⟩
  have hp : IsPGroup 2 (D ⧸ (D ⊓ S).subgroupOf D) := by
    intro q
    obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨1, ?_⟩
    rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf, sq]
    exact ⟨D.mul_mem d.2 d.2, hsq _ d.2⟩
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  exact ⟨n, by rw [Subgroup.relIndex, Subgroup.index_eq_card, hn]⟩

section Core

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

theorem false_of_card_commutator_le (h26ii : Step26ii) (hS : Sec2Setting G A R g E F)
    {D : Subgroup G} (hDN : D ≤ normalizer (sec2S A R E F : Set G))
    (hDel : ∀ a ∈ D, ∀ b ∈ D, a * a ∈ sec2S A R E F ∧ a * b * a⁻¹ * b⁻¹ ∈ sec2S A R E F)
    (hDS : ¬ D ≤ sec2S A R E F)
    (hcard : ∀ d ∈ D, Nat.card (⁅sec2S A R E F, zpowers d⁆ ⊔ sec2Z A E F : Subgroup G) ≤
      4 * (D ⊓ sec2S A R E F).relIndex D) : False := by
  obtain ⟨ha, hb, hc⟩ := h26ii G A R g E F hS
  have hk8 := hc D hDN hDel
  obtain ⟨n, hn⟩ := exists_relIndex_eq_two_pow hDN (fun a ha => (hDel a ha a ha).1)
  have hk1 : (D ⊓ sec2S A R E F).relIndex D ≠ 1 := by
    rw [Ne, relIndex_eq_one]
    exact fun h => hDS (h.trans inf_le_right)
  rcases Nat.lt_or_ge ((D ⊓ sec2S A R E F).relIndex D) 4 with h4 | h4
  · have hk2 : (D ⊓ sec2S A R E F).relIndex D = 2 := by
      have hn2 : n < 2 := by
        by_contra hn2
        have h1 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (not_lt.mp hn2)
        norm_num at h1
        omega
      rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl
      · rw [pow_zero] at hn
        exact absurd hn hk1
      · rw [hn, pow_one]
    obtain ⟨d, hdD, hdS⟩ : ∃ d ∈ D, d ∉ sec2S A R E F := by
      by_contra hcon
      exact hDS fun d hd => by_contra fun h => hcon ⟨d, hd, h⟩
    have h16 := ha d (hDN hdD) hdS (hDel d hdD d hdD).1
    have h1 := hcard d hdD
    rw [hk2] at h1
    omega
  · obtain ⟨d, hdD, h64⟩ := hb D hDN hDel h4
    have h1 := hcard d hdD
    omega

end Core

omit [Finite G] in
theorem subgroupOf_centralizer_normal (Y₀ : Subgroup G) :
    (Y₀.subgroupOf (centralizer (Y₀ : Set G))).Normal := ⟨fun n hn c => by
  rw [mem_subgroupOf] at hn ⊢
  have h1 : (c : G) * n = n * c := (mem_centralizer_iff.mp c.2 n hn).symm
  simpa [h1] using hn⟩

section Quotient

variable {L N : Subgroup G} {Y : Type*} [Group Y]

omit [Finite G] in
theorem card_commutator_sup_eq (hNL : N ≤ L) (π : ↥L →* Y) (hker : π.ker = N.subgroupOf L)
    {A : Subgroup G} (hAL : A ≤ L) {d : G} (hd : d ∈ L) :
    Nat.card (⁅A, zpowers d⁆ ⊔ N : Subgroup G) =
      Nat.card N * Nat.card (⁅(A.subgroupOf L).map π, zpowers (π ⟨d, hd⟩)⁆ : Subgroup Y) := by
  set K₀ : Subgroup L := ⁅A.subgroupOf L, zpowers (⟨d, hd⟩ : L)⁆ with hK₀
  have h1 : (⁅A, zpowers d⁆ ⊔ N : Subgroup G) = (K₀ ⊔ N.subgroupOf L).map L.subtype := by
    rw [Subgroup.map_sup, hK₀, map_commutator, subgroupOf_map_subtype, subgroupOf_map_subtype,
      inf_eq_left.mpr hAL, inf_eq_left.mpr hNL, MonoidHom.map_zpowers]
    rfl
  have h2 : Nat.card ((K₀ ⊔ N.subgroupOf L).map L.subtype) =
      Nat.card ↥(K₀ ⊔ N.subgroupOf L) :=
    card_map_of_injective L.subtype_injective
  have hbot : (N.subgroupOf L).map π = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, hker]
  have h3 : (K₀ ⊔ N.subgroupOf L).map π = ⁅(A.subgroupOf L).map π, zpowers (π ⟨d, hd⟩)⁆ := by
    rw [Subgroup.map_sup, hbot, sup_bot_eq, hK₀, map_commutator, MonoidHom.map_zpowers]
  have h4 : Nat.card ↥(K₀ ⊔ N.subgroupOf L) =
      Nat.card ↥(N.subgroupOf L) * Nat.card ↥((K₀ ⊔ N.subgroupOf L).map π) := by
    have h := relIndex_mul_card (H := π.ker) (K := K₀ ⊔ N.subgroupOf L)
    rw [relIndex_ker, hker, inf_eq_left.mpr le_sup_right] at h
    rw [← h, mul_comm]
  have h5 : Nat.card ↥(N.subgroupOf L) = Nat.card N :=
    Nat.card_congr (subgroupOfEquivOfLe hNL).toEquiv
  rw [h1, h2, h4, h5, h3]

omit [Finite G] in
theorem relIndex_preimage_eq (π : ↥L →* Y) (hπs : Function.Surjective π)
    (hker : π.ker = N.subgroupOf L) {A : Subgroup G} (hNA : N ≤ A) (hAL : A ≤ L)
    (U : Subgroup Y) :
    (((U.comap π).map L.subtype) ⊓ A).relIndex ((U.comap π).map L.subtype) =
      ((A.subgroupOf L).map π).relIndex U := by
  have h1 : ((U.comap π).map L.subtype) ⊓ A = (U.comap π ⊓ A.subgroupOf L).map L.subtype := by
    rw [map_inf_eq _ _ _ L.subtype_injective, subgroupOf_map_subtype, inf_eq_left.mpr hAL]
  rw [h1, relIndex_map_map_of_injective _ _ L.subtype_injective, inf_relIndex_left]
  have h2 : A.subgroupOf L = ((A.subgroupOf L).map π).comap π := by
    rw [comap_map_eq, hker, sup_eq_left.mpr fun x hx => hNA hx]
  conv_lhs => rw [h2]
  rw [relIndex_comap, map_comap_eq_self_of_surjective hπs]

end Quotient

omit [Finite G] in
theorem isElemAbelian_rightConjugate {Y : Type*} [Group Y] {V U : Subgroup Y}
    (hV : IsElemAbelian 2 V) (hUV : U ≤ V) (h : Y) : IsElemAbelian 2 (rightConjugate U h) := by
  refine ⟨isMulCommutative_iff_of_setLike.mpr fun a ha b hb => ?_, fun a ha => ?_⟩
  · rw [mem_rightConjugate_iff] at ha hb
    have h1 := comm_of_mem hV.1 (hUV ha) (hUV hb)
    calc a * b = h⁻¹ * ((h * a * h⁻¹) * (h * b * h⁻¹)) * h := by group
      _ = h⁻¹ * ((h * b * h⁻¹) * (h * a * h⁻¹)) * h := by rw [h1]
      _ = b * a := by group
  · rw [mem_rightConjugate_iff] at ha
    have h1 : h * a ^ 2 * h⁻¹ = 1 := by
      rw [← conj_pow]
      exact hV.2 _ (hUV ha)
    calc a ^ 2 = h⁻¹ * (h * a ^ 2 * h⁻¹) * h := by group
      _ = 1 := by rw [h1]; group

section Setting

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

theorem conj_mem_sec2S_of_mem (h24 : Step24) (h26ii : Step26ii) (h212 : Step212)
    (hS : Sec2Setting G A R g E F) {T₀ : Subgroup G} (hT₀ : sec2P E ⊔ sec2S A R E F ≤ T₀)
    (hT₀s : IsSylowOf 2 T₀ (normalizer (sec2S A R E F : Set G))) {s c : G}
    (hs : s ∈ sec2S A R E F) (hc : c ∈ centralizer (sec2Z A E F : Set G))
    (hcs : c⁻¹ * s * c ∈ T₀) : c⁻¹ * s * c ∈ sec2S A R E F := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S := sec2S A R E F with hSdef
  set Z := sec2Z A E F with hZdef
  set CZ := centralizer (Z : Set G) with hCZdef
  have hSp : Special S Z := special_of h24 hS
  have : (Z.subgroupOf CZ).Normal := subgroupOf_centralizer_normal Z
  set π : ↥CZ →* CZ ⧸ Z.subgroupOf CZ := QuotientGroup.mk' (Z.subgroupOf CZ) with hπdef
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = Z.subgroupOf CZ := QuotientGroup.ker_mk' _
  have hZS : Z ≤ S := hSp.le
  have hSCZ : S ≤ CZ := fun s hs => mem_centralizer_iff.mpr fun c hc => hSp.comm_Z hc hs
  have hZCZ : Z ≤ CZ := hZS.trans hSCZ
  have hST₀ : S ≤ T₀ := le_sup_right.trans hT₀
  have hT₀N : T₀ ≤ normalizer (S : Set G) := hT₀s.le
  have hT₀G : IsSylowOf 2 T₀ ⊤ := ((h212 G A R g E F hS).2 T₀ hT₀ hT₀s).1
  have hT₀NZ : IsSylowOf 2 T₀ (normalizer (Z : Set G)) :=
    hT₀G.of_le (hT₀N.trans (normalizer_le_normalizer_sec2Z hSp)) le_top
  have hT₁ : IsSylowOf 2 (T₀ ⊓ CZ) CZ := hT₀NZ.inf_of_le_normalizer
    (centralizer_le_normalizer _) (normalizer_le_normalizer_centralizer_of Z)
  obtain ⟨Q₁, hQ₁⟩ := hT₁.exists_sylow_eq_subgroupOf
  set PY : Sylow 2 (CZ ⧸ Z.subgroupOf CZ) := Q₁.mapSurjective hπs with hPYdef
  have hPY : (PY : Subgroup (CZ ⧸ Z.subgroupOf CZ)) = ((T₀ ⊓ CZ).subgroupOf CZ).map π := by
    rw [hPYdef, Sylow.coe_mapSurjective, hQ₁]
  have hπeq : ∀ x y : ↥CZ, π x = π y → x⁻¹ * y ∈ Z.subgroupOf CZ := fun x y hxy => by
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
  have hπZ : ∀ x : ↥CZ, (x : G) ∈ Z → π x = 1 := fun x hx => by
    rw [← MonoidHom.mem_ker, hker, mem_subgroupOf]
    exact hx
  set V := (S.subgroupOf CZ).map π with hVdef
  have hmemS : ∀ x : ↥CZ, π x ∈ V → (x : G) ∈ S := by
    rintro x ⟨b, hb, hbe⟩
    have h1 : ((b⁻¹ * x : ↥CZ) : G) ∈ Z := mem_subgroupOf.mp (hπeq b x hbe)
    have hb : (b : G) ∈ S := mem_subgroupOf.mp hb
    have e : (x : G) = (b : G) * ((b⁻¹ * x : ↥CZ) : G) := by simp
    rw [e]
    exact S.mul_mem hb (hZS h1)
  have hVP : V ≤ PY := by
    rw [hPY]
    exact map_mono fun a ha => ⟨hST₀ ha, a.2⟩
  have hVel : IsElemAbelian 2 V := by
    refine ⟨isMulCommutative_iff_of_setLike.mpr ?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      have ha : (a : G) ∈ S := mem_subgroupOf.mp ha
      have hb : (b : G) ∈ S := mem_subgroupOf.mp hb
      rw [← map_mul, ← map_mul, ← mul_inv_eq_one, ← map_inv, ← map_mul]
      refine hπZ _ ?_
      have h1 := hSp.comm_mem ha hb
      simpa [mul_assoc] using h1
    · rintro _ ⟨a, ha, rfl⟩
      have ha : (a : G) ∈ S := mem_subgroupOf.mp ha
      rw [← map_pow]
      refine hπZ _ ?_
      simpa [sq] using hSp.sq _ ha
  have hPN : (PY : Subgroup (CZ ⧸ Z.subgroupOf CZ)) ≤
      normalizer (V : Set (CZ ⧸ Z.subgroupOf CZ)) := by
    rw [hPY]
    refine le_trans (map_mono ?_) (le_normalizer_map π)
    intro t ht
    rw [mem_subgroupOf] at ht
    rw [mem_normalizer_iff]
    intro a
    rw [mem_subgroupOf, mem_subgroupOf]
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using mem_normalizer_iff.mp (hT₀N ht.1) a
  have core : ∀ U : Subgroup (CZ ⧸ Z.subgroupOf CZ), U ≤ PY → IsElemAbelian 2 U → ¬ U ≤ V →
      (∀ w ∈ U, Nat.card (⁅V, zpowers w⁆ : Subgroup (CZ ⧸ Z.subgroupOf CZ)) ≤ V.relIndex U) →
      False := by
    intro U hUP hUel hUV hUc
    refine false_of_card_commutator_le h26ii hS (D := (U.comap π).map CZ.subtype) ?_ ?_ ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩
      have h1 : π a ∈ (PY : Subgroup (CZ ⧸ Z.subgroupOf CZ)) := hUP ha
      rw [hPY] at h1
      obtain ⟨t, ht, hta⟩ := h1
      have hz : ((t⁻¹ * a : ↥CZ) : G) ∈ Z := mem_subgroupOf.mp (hπeq t a hta)
      have ht : (t : G) ∈ T₀ ⊓ CZ := mem_subgroupOf.mp ht
      have e : (a : G) = (t : G) * ((t⁻¹ * a : ↥CZ) : G) := by simp
      have haT : (a : G) ∈ T₀ := by
        rw [e]
        exact T₀.mul_mem ht.1 (hST₀ (hZS hz))
      exact hT₀N haT
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      have ha2 : π a ^ 2 = 1 := hUel.2 _ ha
      have hab : π a * π b = π b * π a := comm_of_mem hUel.1 ha hb
      constructor
      · have h1 : a * a ∈ Z.subgroupOf CZ := by
          rw [← hker, MonoidHom.mem_ker, map_mul, ← sq]
          exact ha2
        exact hZS (mem_subgroupOf.mp h1)
      · have h1 : a * b * a⁻¹ * b⁻¹ ∈ Z.subgroupOf CZ := by
          rw [← hker, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hab]
          group
        exact hZS (mem_subgroupOf.mp h1)
    · intro hDS
      apply hUV
      intro w hw
      obtain ⟨a, rfl⟩ := hπs w
      exact ⟨a, mem_subgroupOf.mpr (hDS ⟨a, hw, rfl⟩), rfl⟩
    · rintro _ ⟨a, ha, rfl⟩
      have h1 := card_commutator_sup_eq hZCZ π hker hSCZ a.2
      have h2 := relIndex_preimage_eq π hπs hker hZS hSCZ U
      rw [hSp.card] at h1
      rw [coe_subtype, h1, h2]
      exact Nat.mul_le_mul_left 4 (hUc _ ha)
  have hwc : ∀ h : CZ ⧸ Z.subgroupOf CZ, rightConjugate V h ≤ PY → rightConjugate V h = V := by
    intro h hhP
    by_contra hne
    have hnle : ¬ rightConjugate V h ≤ V := fun hle =>
      hne (Subgroup.eq_of_le_of_card_ge hle (by rw [rightConjugate_card]))
    have hVhel := isElemAbelian_rightConjugate hVel le_rfl h
    refine core _ hhP hVhel hnle fun w hw => ?_
    have hwN : w ∈ normalizer (V : Set (CZ ⧸ Z.subgroupOf CZ)) := hPN (hhP hw)
    have h1 := Subgroup.card_le_of_le (commutator_zpowers_le_range hVel.1 hwN (hVhel.2 w hw))
    have h2 := card_ker_mul_card_range (commHom hVel.1 hwN)
    have h3 : (V ⊓ rightConjugate V h).subgroupOf V ≤ (commHom hVel.1 hwN).ker := by
      intro e he
      rw [mem_subgroupOf] at he
      rw [mem_ker_commHom]
      exact comm_of_mem hVhel.1 he.2 hw
    have h4 := Subgroup.card_le_of_le h3
    have h5 : Nat.card ((V ⊓ rightConjugate V h).subgroupOf V) =
        Nat.card (V ⊓ rightConjugate V h : Subgroup (CZ ⧸ Z.subgroupOf CZ)) :=
      Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
    have h6 := relIndex_mul_card (H := V) (K := rightConjugate V h)
    rw [rightConjugate_card] at h6
    have hpos : 0 < Nat.card (V ⊓ rightConjugate V h : Subgroup (CZ ⧸ Z.subgroupOf CZ)) :=
      Nat.card_pos
    refine h1.trans (Nat.le_of_mul_le_mul_right ?_ hpos)
    calc Nat.card (commHom hVel.1 hwN).range *
          Nat.card (V ⊓ rightConjugate V h : Subgroup (CZ ⧸ Z.subgroupOf CZ))
        ≤ Nat.card (commHom hVel.1 hwN).range * Nat.card (commHom hVel.1 hwN).ker :=
          Nat.mul_le_mul_left _ (h5 ▸ h4)
      _ = V.relIndex (rightConjugate V h) *
          Nat.card (V ⊓ rightConjugate V h : Subgroup (CZ ⧸ Z.subgroupOf CZ)) := by
          rw [mul_comm, h2, h6]
  by_contra hcsS
  have hsC : s ∈ CZ := hSCZ hs
  have hcsC : c⁻¹ * s * c ∈ CZ := CZ.mul_mem (CZ.mul_mem (CZ.inv_mem hc) hsC) hc
  have hP : (π ⟨c, hc⟩)⁻¹ * π ⟨s, hsC⟩ * π ⟨c, hc⟩ ∈ (PY : Subgroup (CZ ⧸ Z.subgroupOf CZ)) := by
    rw [← map_inv, ← map_mul, ← map_mul, hPY]
    exact ⟨(⟨c, hc⟩ : ↥CZ)⁻¹ * ⟨s, hsC⟩ * ⟨c, hc⟩, mem_subgroupOf.mpr ⟨hcs, hcsC⟩, rfl⟩
  have hnV : (π ⟨c, hc⟩)⁻¹ * π ⟨s, hsC⟩ * π ⟨c, hc⟩ ∉ V := by
    rw [← map_inv, ← map_mul, ← map_mul]
    exact fun hmem => hcsS (hmemS _ hmem)
  obtain ⟨U, hUV, h', hUP, hUV', hUc⟩ := goldschmidt_theorem_four_holds (CZ ⧸ Z.subgroupOf CZ) PY
    V hVP hVel hwc ⟨π ⟨s, hsC⟩, ⟨⟨s, hsC⟩, mem_subgroupOf.mpr hs, rfl⟩, π ⟨c, hc⟩, hP, hnV⟩
  exact core _ hUP (isElemAbelian_rightConjugate hVel hUV h') hUV' hUc

end Setting

end Sec2

end CFSG.ComponentClassification.AS81
