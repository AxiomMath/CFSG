module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.WreathSylow
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.XbarLift
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.FusionEnd

public section

namespace CFSG.EvenSporadicStandard.M23Std

open Subgroup CFSG.Open CFSG.ABGLocalTools

variable {G : Type} [Group G]

abbrev Ybar (L1 : Subgroup G) : Type := Xbar L1 ⧸ fusionOddCore (Xbar L1)

@[expose] def piY (L1 : Subgroup G) : ↥(normalizer (L1 : Set G)) →* Ybar L1 :=
  (QuotientGroup.mk' (fusionOddCore (Xbar L1))).comp (QuotientGroup.mk' _)

theorem piY_apply (L1 : Subgroup G) (x : ↥(normalizer (L1 : Set G))) :
    piY L1 x = QuotientGroup.mk (QuotientGroup.mk x : Xbar L1) := rfl

theorem piY_surjective (L1 : Subgroup G) : Function.Surjective (piY L1) :=
  (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)

@[expose] def preimageY (L1 : Subgroup G) (M : Subgroup (Ybar L1)) : Subgroup G :=
  (M.comap (piY L1)).map (normalizer (L1 : Set G)).subtype

theorem mem_preimageY {L1 : Subgroup G} {M : Subgroup (Ybar L1)} {g : G} :
    g ∈ preimageY L1 M ↔ ∃ hg : g ∈ normalizer (L1 : Set G), piY L1 ⟨g, hg⟩ ∈ M := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨hg, h⟩
    exact ⟨⟨g, hg⟩, h, rfl⟩

theorem mem_preimageY_iff {L1 : Subgroup G} {M : Subgroup (Ybar L1)} {g : G}
    (hg : g ∈ normalizer (L1 : Set G)) : g ∈ preimageY L1 M ↔ piY L1 ⟨g, hg⟩ ∈ M :=
  ⟨fun h => (mem_preimageY.1 h).2, fun h => mem_preimageY.2 ⟨hg, h⟩⟩

variable {L : Subgroup G} {z t : G} {F L1 N : Subgroup G}

namespace Setup

variable (S : Setup L z t F L1 N)

include S

theorem isPGroup_L1 : IsPGroup 2 L1 :=
  IsPGroup.of_card (n := 8) (S.L1_card.trans (by norm_num))

theorem L1_le_of_isSylowOf [Finite G] {P : Subgroup G}
    (hP : IsSylowOf 2 P (normalizer (L1 : Set G))) : L1 ≤ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hP.exists_sylow_eq_subgroupOf
  have hnormal : (L1.subgroupOf (normalizer (L1 : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).2 le_rfl
  have hpg : IsPGroup 2 (L1.subgroupOf (normalizer (L1 : Set G))) := S.isPGroup_L1.comap_subtype
  have hle := IsPGroup.le_sylow_of_normal (N := L1.subgroupOf (normalizer (L1 : Set G))) hpg Q
  intro l hl
  have h1 : (⟨l, Subgroup.le_normalizer hl⟩ : ↥(normalizer (L1 : Set G))) ∈
      L1.subgroupOf (normalizer (L1 : Set G)) := hl
  have h2 := hle h1
  rw [hQ] at h2
  exact h2

theorem zbar_sq : piY L1 S.zX * piY L1 S.zX = 1 := by
  rw [← map_mul]
  have : S.zX * S.zX = 1 := Subtype.ext (by simpa using S.one.z_mul_self)
  rw [this, map_one]

theorem exists_sylow_X [Finite G] (hL2 : ¬ 256 ∣ Nat.card L) :
    ∃ P : Subgroup G, IsSylowOf 2 P (normalizer (L1 : Set G)) ∧ z ∈ P ∧
      IsSylowOf 2 (P ⊓ centralizer ({z} : Set G)) (centralizer ({z} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨D, hD⟩ : ∃ D : Subgroup G, D = normalizer (F : Set G) ⊓ L := ⟨_, rfl⟩
  obtain ⟨Cz, hCz⟩ : ∃ Cz : Subgroup G,
      Cz = normalizer (L1 : Set G) ⊓ centralizer ({z} : Set G) := ⟨_, rfl⟩
  have hCzeq : Cz = zpowers z ⊔ D := by rw [hCz, hD]; exact S.inf_centralizer_eq
  have hDL : D ≤ L := hD ▸ inf_le_right
  have hCzX : Cz ≤ normalizer (L1 : Set G) := hCz ▸ inf_le_left
  have hCzC : Cz ≤ centralizer ({z} : Set G) := hCz ▸ inf_le_right
  have hzC : z ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.2 rfl
  have hLC : L ≤ centralizer ({z} : Set G) := fun l hl =>
    mem_centralizer_singleton_iff.2 (S.one.z_comm l hl).symm
  have hCG : centralizer ({z} : Set G) = zpowers z ⊔ L := by
    apply le_antisymm
    · intro g hg
      obtain ⟨l, hl, hcases⟩ := S.one.centralizer_z g (mem_centralizer_singleton_iff.1 hg).symm
      rcases hcases with rfl | rfl
      · exact mem_sup_right hl
      · exact mul_mem (mem_sup_right hl) (mem_sup_left (mem_zpowers z))
    · exact sup_le (zpowers_le.2 hzC) hLC
  have hcardsup : ∀ H : Subgroup G, H ≤ L → Nat.card ↥(zpowers z ⊔ H) = 2 * Nat.card H := by
    intro H hHL
    have hHc : H ≤ centralizer (zpowers z : Set G) := by
      intro d hd
      rw [mem_centralizer_iff]
      intro a ha
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 ha
      exact (Commute.zpow_left (show Commute z d from S.one.z_comm d (hHL hd)) k).eq
    have e := internalProdEquiv hHc (disjoint_zpowers S.one hHL).symm
    rw [← Nat.card_congr e.toEquiv, Nat.card_prod, card_zpowers_z S.one]
  have hodd1 : ¬ 2 ∣ Cz.relIndex (centralizer ({z} : Set G)) := by
    intro h2
    have h1 := Subgroup.relIndex_mul_card Cz (centralizer ({z} : Set G))
    rw [inf_of_le_left hCzC] at h1
    have hcCz : Nat.card Cz = 2 * Nat.card D := by rw [hCzeq]; exact hcardsup D hDL
    have hcC : Nat.card (centralizer ({z} : Set G)) = 2 * Nat.card L := by
      rw [hCG]; exact hcardsup L le_rfl
    rw [hcCz, hcC] at h1
    have h3 : Cz.relIndex (centralizer ({z} : Set G)) * Nat.card D = Nat.card L := by
      have : 2 * (Cz.relIndex (centralizer ({z} : Set G)) * Nat.card D) = 2 * Nat.card L := by
        rw [← h1]; ring
      omega
    have h128 : 128 ∣ Nat.card D := hD ▸ S.nd.N_two
    apply hL2
    rw [← h3]
    exact (show (256 : ℕ) = 2 * 128 by norm_num) ▸ Nat.mul_dvd_mul h2 h128
  obtain ⟨Q, hQ⟩ := exists_isSylowOf 2 Cz
  have hzCz : z ∈ Cz := hCz ▸ mem_inf.2 ⟨S.zX.2, hzC⟩
  have hz2g : IsPGroup 2 (zpowers z) := IsPGroup.of_card (n := 1) (by
    rw [card_zpowers_z S.one]; norm_num)
  have hQN : Q ≤ normalizer (zpowers z : Set G) := by
    refine fun q hq => Subgroup.centralizer_le_normalizer _ ?_
    rw [mem_centralizer_iff]
    intro a ha
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 ha
    have hqz : z * q = q * z := (mem_centralizer_singleton_iff.1 (hCzC (hQ.le hq))).symm
    exact (Commute.zpow_left (show Commute z q from hqz) k).eq
  have hzQ : z ∈ Q := by
    have hpg : IsPGroup 2 (Q ⊔ zpowers z : Subgroup G) :=
      hQ.isPGroup.to_sup_of_normal_right' hz2g hQN
    have := hQ.eq_of_le (le_sup_left : Q ≤ Q ⊔ zpowers z)
      (sup_le hQ.le (zpowers_le.2 hzCz)) hpg
    rw [← this]
    exact mem_sup_right (mem_zpowers z)
  have hQX : IsPGroup 2 (Q.subgroupOf (normalizer (L1 : Set G))) := hQ.isPGroup.comap_subtype
  obtain ⟨P', hP'⟩ := hQX.exists_le_sylow
  have hPsyl : IsSylowOf 2 ((P' : Subgroup ↥(normalizer (L1 : Set G))).map
      (normalizer (L1 : Set G)).subtype) (normalizer (L1 : Set G)) := ⟨P', rfl⟩
  set P := (P' : Subgroup ↥(normalizer (L1 : Set G))).map (normalizer (L1 : Set G)).subtype
    with hPdef
  have hQP : Q ≤ P := fun q hq =>
    ⟨⟨q, hCzX (hQ.le hq)⟩, hP' (show (⟨q, hCzX (hQ.le hq)⟩ : ↥(normalizer (L1 : Set G))) ∈
      Q.subgroupOf (normalizer (L1 : Set G)) from hq), rfl⟩
  have hPC : P ⊓ centralizer ({z} : Set G) = Q :=
    hQ.eq_of_le (le_inf hQP (hQ.le.trans hCzC))
      (hCz ▸ inf_le_inf_right _ hPsyl.le) (hPsyl.isPGroup.to_inf_left)
  refine ⟨P, hPsyl, hQP hzQ, ?_⟩
  rw [hPC, isSylowOf_iff]
  refine ⟨hQ.le.trans hCzC, hQ.isPGroup, ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex Q Cz (centralizer ({z} : Set G)) hQ.le hCzC]
  exact fun h => (Nat.prime_two.dvd_mul.1 h).elim (isSylowOf_iff.1 hQ).2.2 hodd1

theorem exists_conj_mem_preimage_of_wreath [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {N1 N2 : Subgroup (Ybar L1)}
    (hcomm : ∀ a ∈ N1, ∀ b ∈ N2, a * b = b * a) (hdisj : Disjoint N1 N2)
    (hnorm : (N1 ⊔ N2).Normal) (hidx : (N1 ⊔ N2).index = 2)
    (hz0 : piY L1 S.zX ∉ N1 ⊔ N2)
    (hconj : N1.map (MulAut.conj (piY L1 S.zX)).toMonoidHom = N2)
    {P : Subgroup G} (hP : IsSylowOf 2 P (normalizer (L1 : Set G))) (hzP : z ∈ P)
    (hT : IsSylowOf 2 (P ⊓ centralizer ({z} : Set G)) (centralizer ({z} : Set G))) :
    ∃ g : G, g⁻¹ * z * g ∈ P ⊓ preimageY L1 (N1 ⊔ N2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := normalizer (L1 : Set G) with hX
  set zb : Ybar L1 := piY L1 S.zX with hzb
  have hz2 : z * z = 1 := S.one.z_mul_self
  have hz1 : z ≠ 1 := S.one.z_ne_one
  have hPX : P ≤ X := hP.le
  have hL1P : L1 ≤ P := S.L1_le_of_isSylowOf hP
  have hP2 : IsPGroup 2 P := hP.isPGroup
  have hzb2 : zb * zb = 1 := S.zbar_sq
  have hzbi : zb⁻¹ = zb := inv_eq_of_mul_eq_one_right hzb2
  have hN1 : ∀ a ∈ N1, zb * a * zb ∈ N2 := fun a ha => by
    rw [← hconj]
    exact ⟨a, ha, by simp [hzbi]⟩
  have hN2 : ∀ b ∈ N2, zb * b * zb ∈ N1 := fun b hb => by
    rw [← hconj] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    have : zb * (MulAut.conj zb).toMonoidHom a * zb = a := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hzbi]
      calc zb * (zb * a * zb) * zb = (zb * zb) * a * (zb * zb) := by group
        _ = a := by rw [hzb2]; group
    rw [this]
    exact ha
  obtain ⟨Q, hQ⟩ := hP.exists_sylow_eq_subgroupOf
  set T : Subgroup (Ybar L1) := (P.subgroupOf X).map (piY L1) with hT'
  have hQT : ((Q.mapSurjective (piY_surjective L1) : Sylow 2 (Ybar L1)) : Subgroup (Ybar L1)) =
      T := by
    rw [Sylow.coe_mapSurjective, hQ]
  have hTsyl : IsSylowOf 2 T ⊤ := by
    refine isSylowOf_iff.2 ⟨le_top, ?_, ?_⟩
    · rw [← hQT]; exact Sylow.isPGroup' _
    · rw [Subgroup.relIndex_top_right, ← hQT]; exact Sylow.not_dvd_index _
  have hmemT : ∀ x : G, ∀ hxX : x ∈ X, x ∈ P → piY L1 ⟨x, hxX⟩ ∈ T := fun x hxX hxP =>
    ⟨⟨x, hxX⟩, hxP, rfl⟩
  have hzT : zb ∈ T := hmemT z S.zX.2 hzP
  have hfus : ∀ x ∈ P, x * x = 1 → x ∉ P ⊓ preimageY L1 (N1 ⊔ N2) →
      ∃ s ∈ P, x = s⁻¹ * z * s := by
    intro x hxP hx2 hxS0
    have hxX : x ∈ X := hPX hxP
    have hxb_not : piY L1 ⟨x, hxX⟩ ∉ N1 ⊔ N2 := fun h =>
      hxS0 (mem_inf.2 ⟨hxP, (mem_preimageY_iff hxX).2 h⟩)
    have hxb2 : piY L1 ⟨x, hxX⟩ * piY L1 ⟨x, hxX⟩ = 1 := by
      rw [← map_mul]
      have : (⟨x, hxX⟩ : ↥X) * ⟨x, hxX⟩ = 1 := Subtype.ext (by simpa using hx2)
      rw [this, map_one]
    have hzx : zb * piY L1 ⟨x, hxX⟩ ∈ N1 ⊔ N2 :=
      (Subgroup.mul_mem_iff_of_index_two hidx).2 (iff_of_false hz0 hxb_not)
    obtain ⟨c, hcT, hxc⟩ := exists_mem_conj_of_wreath_sylow hTsyl hnorm hdisj hcomm hzb2 hN1 hN2
      hzT (hmemT x hxX hxP) hxb2 hzx
    obtain ⟨⟨β, hβX⟩, hβP, rfl⟩ := hcT
    have hβP' : β ∈ P := hβP
    have hyz : β * x * β⁻¹ * z ∈ X :=
      X.mul_mem (X.mul_mem (X.mul_mem hβX hxX) (X.inv_mem hβX)) S.zX.2
    have hyP : β * x * β⁻¹ ∈ P := P.mul_mem (P.mul_mem hβP' hxP) (P.inv_mem hβP')
    have hy2 : β * x * β⁻¹ * (β * x * β⁻¹) = 1 := by
      calc β * x * β⁻¹ * (β * x * β⁻¹) = β * (x * x) * β⁻¹ := by group
        _ = 1 := by rw [hx2]; group
    have h1 : piY L1 ⟨β * x * β⁻¹ * z, hyz⟩ = 1 := by
      have : (⟨β * x * β⁻¹ * z, hyz⟩ : ↥X) = ⟨β, hβX⟩ * ⟨x, hxX⟩ * ⟨β, hβX⟩⁻¹ * S.zX := rfl
      rw [this, map_mul, map_mul, map_mul, map_inv, hxc]
      calc piY L1 ⟨β, hβX⟩ * ((piY L1 ⟨β, hβX⟩)⁻¹ * zb * piY L1 ⟨β, hβX⟩) *
            (piY L1 ⟨β, hβX⟩)⁻¹ * zb = zb * zb := by group
        _ = 1 := hzb2
    obtain ⟨s, hsP, hs⟩ := S.exists_conj_of_image_eq_one hP2 hL1P hzP (y := β * x * β⁻¹) hyP hy2
      hyz h1
    refine ⟨s * β, P.mul_mem hsP hβP', ?_⟩
    calc x = β⁻¹ * (β * x * β⁻¹) * β := by group
      _ = β⁻¹ * (s⁻¹ * z * s) * β := by rw [hs]
      _ = (s * β)⁻¹ * z * (s * β) := by group
  have hz0' : z ∉ P ⊓ preimageY L1 (N1 ⊔ N2) := fun h =>
    hz0 ((mem_preimageY_iff S.zX.2).1 (mem_inf.1 h).2)
  have hidx2 : (P ⊓ preimageY L1 (N1 ⊔ N2)).relIndex P = 2 := by
    refine Subgroup.index_eq_two_iff.2 ⟨⟨z, hzP⟩, fun b => ?_⟩
    have hbX : (b : G) ∈ X := hPX b.2
    have hbzX : (b : G) * z ∈ X := X.mul_mem hbX S.zX.2
    have key : ((b : G) * z ∈ preimageY L1 (N1 ⊔ N2)) ↔
        ¬ ((b : G) ∈ preimageY L1 (N1 ⊔ N2)) := by
      rw [mem_preimageY_iff hbzX, mem_preimageY_iff hbX]
      have : piY L1 ⟨(b : G) * z, hbzX⟩ = piY L1 ⟨(b : G), hbX⟩ * zb := rfl
      rw [this, Subgroup.mul_mem_iff_of_index_two hidx]
      exact ⟨fun h h' => hz0 (h.1 h'), fun h => ⟨fun h' => absurd h' h, fun h' => absurd h' hz0⟩⟩
    show Xor (b * ⟨z, hzP⟩ ∈ (P ⊓ preimageY L1 (N1 ⊔ N2)).subgroupOf P)
      (b ∈ (P ⊓ preimageY L1 (N1 ⊔ N2)).subgroupOf P)
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, mem_inf]
    by_cases hB : (b : G) ∈ preimageY L1 (N1 ⊔ N2)
    · exact Or.inr ⟨⟨b.2, hB⟩, fun h => key.1 h.2 hB⟩
    · exact Or.inl ⟨⟨P.mul_mem b.2 hzP, key.2 hB⟩, fun h => hB h.2⟩
  exact exists_conj_mem_of_fusion hnonab hz2 hz1 hP2 hzP hT inf_le_left hidx2 hz0' hfus

end Setup

end CFSG.EvenSporadicStandard.M23Std
