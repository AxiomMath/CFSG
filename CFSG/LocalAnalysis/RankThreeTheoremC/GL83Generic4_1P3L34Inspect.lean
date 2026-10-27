module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Struct
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34KFacts
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.InvariantTwoWithin
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Inspectb
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Inspectc

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

theorem l34_stepG (hS : Setting G) (hU0 : FullCoreLocal G) (hD1 : TheoremD1 G)
    (hK1 : KFactL34TwoSignalizer) (hK2 : KFactL34Three) (hK4 : KFactL34Borel)
    (hK5 : KFactL34Graph) (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G}
    (hM : IsCoreMaxLocal 3 P M) {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G}
    (hJ : IsL34Normal M x J)
    (hKM : l34Img x J M ⊓ l34Img x J J =
      normalizer ((l34Img x J ((P : Subgroup G) ⊓ J) : Subgroup (L34Quot x J)) :
        Set (L34Quot x J)) ⊓ l34Img x J J)
    {U : Subgroup G} (hU : IsElemAbelian 3 U) (hUc : Nat.card U = 3 ^ 2)
    (hUP : U ≤ (P : Subgroup G)) (hxU : x ∈ U) (hUJ : U ⊓ J ≠ ⊥) {S₁ : Subgroup G}
    (hS₁ : rankTwoMaximalInvariantTwoSubgroup U S₁)
    (hS₁J : invariantTwoMaximalWithin U J (S₁ ⊓ J))
    (hC : ∀ u ∈ U, u ∉ zpowers x → centralizer ({u} : Set G) ≤ M) :
    IsSylowOf 2 (l34Img x J (S₁ ⊓ J)) (l34Img x J J) ∧
    S₁ ⊓ centralizer ({x} : Set G) = (S₁ ⊓ J) ⊔ (S₁ ⊓ centralizer (U : Set G)) ∧
    Nat.card ↥(S₁ ⊓ centralizer (U : Set G)) ≤ 2 ∧
    S₁ ⊓ M ⊓ centralizer ({x} : Set G) = S₁ ⊓ centralizer (U : Set G) ∧
    ∀ w ∈ S₁ ⊓ centralizer (U : Set G), w ≠ 1 →
      ¬ (l34Img x J (zpowers w) ≤ centralizer ((l34Img x J ((P : Subgroup G) ⊓ J) :
        Subgroup (L34Quot x J)) : Set (L34Quot x J))) := by
  have hprime : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hprime⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hPM, -⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  have hx1 : x ≠ 1 := hgen.2.1.2.1
  have hx3 : x ^ 3 = 1 := hgen.2.1.2.2.1
  have hJC : J ≤ centralizer ({x} : Set G) := hJ.le_centralizer
  have hNJ : centralizer ({x} : Set G) ≤ normalizer (J : Set G) := hJ.centralizer_le
  have hxJc : ∀ j ∈ J, x * j = j * x := fun j hj =>
    (mem_centralizer_singleton_iff.mp (hJC hj)).symm
  have hUC : U ≤ centralizer ({x} : Set G) := fun g hg => mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (hU.1.is_comm.comm ⟨g, hg⟩ ⟨x, hxU⟩))
  obtain ⟨⟨u, hu⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hUJ
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  have huU : u ∈ U := hu.1
  have huJ : u ∈ J := hu.2
  have hu3 : u ^ 3 = 1 := hU.2 u huU
  have huo : orderOf u = 3 := orderOf_eq_prime hu3 hu1'
  have huC : u ∈ centralizer ({x} : Set G) := hUC huU
  have huM : u ∈ M := hPM (hUP huU)
  have hxJ : x ∉ J := fun hxJ =>
    hx1 (l34insp_eq_one_of_three hK1 hK2 hJ hxJ hx3 (l34insp_hom_self hJ))
  have hxu : x ∉ zpowers u := fun h => hxJ (zpowers_le.mpr huJ h)
  have hux : u ∉ zpowers x := by
    intro h
    have heq : zpowers u = zpowers x := Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr h) (by
      rw [Nat.card_zpowers, Nat.card_zpowers, huo, orderOf_eq_prime hx3 hx1])
    exact hxu (heq ▸ mem_zpowers x)
  have hUxu : U ≤ zpowers x ⊔ zpowers u := by
    have hcard := CFSG.RankThree.PartOne.Planes.card_sup_zpowers hprime (zpowers u) hx3 hxu
      (fun e he => by
        obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp he
        exact (Commute.zpow_right (hxJc u huJ : Commute x u) m).eq.symm)
    rw [Nat.card_zpowers, huo] at hcard
    have hle : zpowers u ⊔ zpowers x ≤ U := sup_le (zpowers_le.mpr huU) (zpowers_le.mpr hxU)
    have heq : zpowers u ⊔ zpowers x = U :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hUc, hcard]; norm_num)
    rw [sup_comm, heq]
  have hS₁2 : IsPGroup 2 S₁ := hS₁.1
  have hUS₁ : U ≤ normalizer (S₁ : Set G) := hS₁.2.1
  have hinj : ∀ c : ↥(centralizer ({x} : Set G)), (c : G) ∈ S₁ → l34Hom x J c = 1 → c = 1 :=
    fun c hc h1 => by
      obtain ⟨k, hk⟩ := hS₁2 ⟨c, hc⟩
      exact l34insp_eq_one_of_two hS hU0 hD1 hK1 hK2 hp hM hgen hJ (k := k)
        (by simpa using congrArg Subtype.val hk) h1
  have hsyl : IsSylowOf 2 (l34Img x J (S₁ ⊓ J)) (l34Img x J J) :=
    l34insp_sylow hS hU0 hK1 hK2 hK4 hp hM hgen hJ (P.isPGroup'.to_le hUP) huU huJ hu1' hu3
      hUxu hS₁J
  obtain ⟨hKn, hKc, hKt⟩ := l34_quot_data hS hU0 hK1 hK2 hp hM hgen hJ
  have huK : l34Hom x J ⟨u, huC⟩ ∈ l34Img x J J :=
    ⟨⟨u, huC⟩, Subgroup.mem_subgroupOf.mpr huJ, rfl⟩
  have hAK : l34Img x J S₁ ⊓ l34Img x J J = l34Img x J (S₁ ⊓ J) :=
    hsyl.eq_of_le (le_inf (Subgroup.map_mono fun c hc => (Subgroup.mem_subgroupOf.mp hc).1)
      hsyl.le) inf_le_right (((hS₁2.comap_subtype (K := centralizer ({x} : Set G))).map
        (l34Hom x J)).to_le inf_le_left)
  have hcomm : ∀ b ∈ S₁ ⊓ centralizer ({x} : Set G), b⁻¹ * u⁻¹ * b * u ∈ S₁ ⊓ J := by
    intro b hb
    have hgS₁ : b⁻¹ * u⁻¹ * b * u ∈ S₁ := by
      have h1 : u⁻¹ * b * u⁻¹⁻¹ ∈ S₁ := (mem_normalizer_iff.mp (hUS₁ (U.inv_mem huU)) b).mp hb.1
      rw [inv_inv] at h1
      have h2 : b⁻¹ * u⁻¹ * b * u = b⁻¹ * (u⁻¹ * b * u) := by group
      rw [h2]
      exact S₁.mul_mem (S₁.inv_mem hb.1) h1
    have hgC : b⁻¹ * u⁻¹ * b * u ∈ centralizer ({x} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hb.2)
        (Subgroup.inv_mem _ huC)) hb.2) huC
    have he : (⟨b⁻¹ * u⁻¹ * b * u, hgC⟩ : ↥(centralizer ({x} : Set G))) =
        (⟨b, hb.2⟩ : ↥(centralizer ({x} : Set G)))⁻¹ * (⟨u, huC⟩)⁻¹ * ⟨b, hb.2⟩ * ⟨u, huC⟩ := rfl
    have hgK : l34Hom x J ⟨_, hgC⟩ ∈ l34Img x J J := by
      rw [he, map_mul, map_mul, map_mul, map_inv, map_inv]
      refine Subgroup.mul_mem _ ?_ huK
      have h1 := hKn.conj_mem _ (Subgroup.inv_mem _ huK) (l34Hom x J ⟨b, hb.2⟩)⁻¹
      rwa [inv_inv] at h1
    have hgA : l34Hom x J ⟨_, hgC⟩ ∈ l34Img x J S₁ :=
      ⟨⟨_, hgC⟩, Subgroup.mem_subgroupOf.mpr hgS₁, rfl⟩
    have hgS : l34Hom x J ⟨_, hgC⟩ ∈ l34Img x J (S₁ ⊓ J) := hAK ▸ ⟨hgA, hgK⟩
    obtain ⟨a, ha, hag⟩ := hgS
    have ha' : (a : G) ∈ S₁ ⊓ J := Subgroup.mem_subgroupOf.mp ha
    have h1 : a⁻¹ * ⟨_, hgC⟩ = 1 := hinj _ (S₁.mul_mem (S₁.inv_mem ha'.1) hgS₁)
      (by rw [map_mul, map_inv, hag, inv_mul_cancel])
    have h2 : (⟨_, hgC⟩ : ↥(centralizer ({x} : Set G))) = a := by
      calc (⟨_, hgC⟩ : ↥(centralizer ({x} : Set G))) = a * (a⁻¹ * ⟨_, hgC⟩) := by group
        _ = a := by rw [h1, mul_one]
    have h3 : b⁻¹ * u⁻¹ * b * u = (a : G) := congrArg Subtype.val h2
    rw [h3]
    exact ha'
  have hS₂B : S₁ ⊓ J ≤ S₁ ⊓ centralizer ({x} : Set G) := le_inf inf_le_left (inf_le_right.trans hJC)
  have hBN : S₁ ⊓ centralizer ({x} : Set G) ≤ normalizer ((S₁ ⊓ J : Subgroup G) : Set G) :=
    fun b hb => Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hb.1, hNJ hb.2⟩
  have huN : u ∈ normalizer ((S₁ ⊓ J : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hUS₁ huU, hNJ huC⟩
  have hdec : ∀ b ∈ S₁ ⊓ centralizer ({x} : Set G),
      ∃ c ∈ S₁ ⊓ centralizer (U : Set G), c⁻¹ * b ∈ S₁ ⊓ J := by
    intro b hb
    obtain ⟨c, hcB, hcu, hcb⟩ :=
      l34insp_exists_fixed hS₂B (hS₁2.to_le inf_le_left) hBN huN huo hcomm hb
    refine ⟨c, ⟨hcB.1, mem_centralizer_iff.mpr fun h hh => ?_⟩, hcb⟩
    have hle : zpowers x ⊔ zpowers u ≤ centralizer ({c} : Set G) := sup_le
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
        (mem_centralizer_singleton_iff.mp hcB.2).symm))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hcu.symm))
    exact mem_centralizer_singleton_iff.mp (hle (hUxu hh))
  have hWC : S₁ ⊓ centralizer (U : Set G) ≤ centralizer ({x} : Set G) := fun w hw =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hw.2 x hxU).symm
  have hWu : ∀ w ∈ S₁ ⊓ centralizer (U : Set G), w * u = u * w := fun w hw =>
    (mem_centralizer_iff.mp hw.2 u huU).symm
  have hWM : S₁ ⊓ centralizer (U : Set G) ≤ M := fun w hw =>
    hC u huU hux (mem_centralizer_singleton_iff.mpr (hWu w hw))
  have hpart2 : S₁ ⊓ centralizer ({x} : Set G) = (S₁ ⊓ J) ⊔ (S₁ ⊓ centralizer (U : Set G)) := by
    refine le_antisymm (fun b hb => ?_) (sup_le hS₂B (le_inf inf_le_left hWC))
    obtain ⟨c, hcW, hcb⟩ := hdec b hb
    have h : b = c * (c⁻¹ * b) := by group
    rw [h]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hcW) (Subgroup.mem_sup_left hcb)
  have huo' : orderOf (l34Hom x J ⟨u, huC⟩) = 3 := by
    refine orderOf_eq_prime ?_ fun h => hu1' (l34insp_eq_one_of_three hK1 hK2 hJ huJ hu3 h)
    rw [← map_pow]
    have : (⟨u, huC⟩ : ↥(centralizer ({x} : Set G))) ^ 3 = 1 := Subtype.ext (by simpa using hu3)
    rw [this, map_one]
  have huN' := l34insp_hom_mem_normalizer x J (S₁ ⊓ J) (u := ⟨u, huC⟩) huN
  have hWt2 : IsPGroup 2 (l34Img x J (S₁ ⊓ centralizer (U : Set G))) :=
    (((hS₁2.to_le inf_le_left).comap_subtype (K := centralizer ({x} : Set G)))).map _
  have hWtN : l34Img x J (S₁ ⊓ centralizer (U : Set G)) ≤
      normalizer ((l34Img x J (S₁ ⊓ J) : Subgroup (L34Quot x J)) : Set (L34Quot x J)) := by
    rintro _ ⟨c, hc, rfl⟩
    exact l34insp_hom_mem_normalizer x J (S₁ ⊓ J)
      (hBN ⟨(Subgroup.mem_subgroupOf.mp hc).1, c.2⟩)
  have hWtC : l34Img x J (S₁ ⊓ centralizer (U : Set G)) ≤
      centralizer ({l34Hom x J ⟨u, huC⟩} : Set (L34Quot x J)) := by
    rintro _ ⟨c, hc, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hWu c (Subgroup.mem_subgroupOf.mp hc))
  obtain ⟨hWtcard, hWtgraph⟩ := hK5 _ (l34Img x J J) hKn hKc hKt (l34Img x J (S₁ ⊓ J)) hsyl.le
    hsyl _ huK huo' huN' _ hWt2 hWtN hWtC
  have hinjW : Function.Injective ((l34Hom x J).comp
      ((S₁ ⊓ centralizer (U : Set G)).subgroupOf (centralizer ({x} : Set G))).subtype) := by
    rw [injective_iff_map_eq_one]
    intro w hw
    exact Subtype.ext (hinj _ (Subgroup.mem_subgroupOf.mp w.2).1 hw)
  have hcardW : Nat.card ↥(S₁ ⊓ centralizer (U : Set G)) =
      Nat.card ↥(l34Img x J (S₁ ⊓ centralizer (U : Set G))) := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWC).toEquiv,
      Nat.card_congr (MonoidHom.ofInjective hinjW).toEquiv, MonoidHom.range_comp,
      Subgroup.range_subtype]
    rfl
  have hbot := l34insp_inf_eq_bot hS hU0 hK1 hK2 hp hM hgen hJ hKM (hUP huU) huJ huM hu1' hu3
    inf_le_right (hS₁2.to_le inf_le_left) huN
  have hpart4 : S₁ ⊓ M ⊓ centralizer ({x} : Set G) = S₁ ⊓ centralizer (U : Set G) := by
    refine le_antisymm (fun s hs => ?_) (le_inf (le_inf inf_le_left hWM) hWC)
    obtain ⟨c, hcW, hcs⟩ := hdec s ⟨hs.1.1, hs.2⟩
    have haM : c⁻¹ * s ∈ M := M.mul_mem (M.inv_mem (hWM hcW)) hs.1.2
    have haC : c⁻¹ * s ∈ centralizer ({x} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (hWC hcW)) hs.2
    have h1 : l34Hom x J ⟨c⁻¹ * s, haC⟩ = 1 := by
      have h : l34Hom x J ⟨c⁻¹ * s, haC⟩ ∈ l34Img x J (S₁ ⊓ J) ⊓ l34Img x J M :=
        ⟨⟨⟨_, haC⟩, Subgroup.mem_subgroupOf.mpr hcs, rfl⟩,
          ⟨⟨_, haC⟩, Subgroup.mem_subgroupOf.mpr haM, rfl⟩⟩
      rw [hbot] at h
      exact h
    have h2 : c⁻¹ * s = 1 := congrArg Subtype.val (hinj _ hcs.1 h1)
    have h3 : s = c := by
      calc s = c * (c⁻¹ * s) := by group
        _ = c := by rw [h2, mul_one]
    rw [h3]
    exact hcW
  obtain ⟨hTe, hTc, hTK⟩ := l34_T_data hS hU0 hK1 hK2 hp hM hgen hJ
  have huT : l34Hom x J ⟨u, huC⟩ ∈ l34Img x J ((P : Subgroup G) ⊓ J) :=
    ⟨⟨u, huC⟩, Subgroup.mem_subgroupOf.mpr ⟨hUP huU, huJ⟩, rfl⟩
  have hpart5 : ∀ w ∈ S₁ ⊓ centralizer (U : Set G), w ≠ 1 →
      ¬ (l34Img x J (zpowers w) ≤ centralizer ((l34Img x J ((P : Subgroup G) ⊓ J) :
        Subgroup (L34Quot x J)) : Set (L34Quot x J))) := by
    intro w hw hw1 hle
    have hwc : l34Hom x J ⟨w, hWC hw⟩ ∈ centralizer ((l34Img x J ((P : Subgroup G) ⊓ J) :
        Subgroup (L34Quot x J)) : Set (L34Quot x J)) :=
      hle ⟨⟨w, hWC hw⟩, Subgroup.mem_subgroupOf.mpr (mem_zpowers w), rfl⟩
    have hwW : l34Hom x J ⟨w, hWC hw⟩ ∈ l34Img x J (S₁ ⊓ centralizer (U : Set G)) :=
      ⟨⟨w, hWC hw⟩, Subgroup.mem_subgroupOf.mpr hw, rfl⟩
    have hw1' : l34Hom x J ⟨w, hWC hw⟩ ≠ 1 := fun h =>
      hw1 (congrArg Subtype.val (hinj _ hw.1 h))
    have hTle : l34Img x J ((P : Subgroup G) ⊓ J) ≤ zpowers (l34Hom x J ⟨u, huC⟩) := by
      intro t ht
      refine hWtgraph _ hwW hw1' t ⟨mem_centralizer_singleton_iff.mpr ?_, hTK ht⟩
        (mem_centralizer_iff.mp hwc t ht).symm
      exact congrArg Subtype.val (hTe.1.is_comm.comm ⟨t, ht⟩ ⟨_, huT⟩)
    have h := Subgroup.card_le_of_le hTle
    rw [hTc, Nat.card_zpowers, huo'] at h
    norm_num at h
  exact ⟨hsyl, hpart2, hcardW ▸ hWtcard, hpart4, hpart5⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
