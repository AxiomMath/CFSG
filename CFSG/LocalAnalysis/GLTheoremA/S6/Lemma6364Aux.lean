module

public import CFSG.LocalAnalysis.GLTheoremA.S6.Defs
public import CFSG.LocalAnalysis.GLTheoremA.PComp

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

namespace L6364

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem inf_centModSubgroup_eq_zpowers {B L : Subgroup G} {x : G} (hx : x ∈ B)
    (h : CentModEqZpowers p B L x) : B ⊓ centModSubgroup p L = Subgroup.zpowers x := by
  ext b
  constructor
  · rintro ⟨hb, hbc⟩
    exact (h b hb).1 (centMod_iff.2 hbc)
  · intro hb
    have hbB : b ∈ B := Subgroup.zpowers_le.2 hx hb
    exact ⟨hbB, centMod_iff.1 ((h b hbB).2 hb)⟩

theorem card_inf_centModSubgroup (hp : p.Prime) {B L : Subgroup G} {x : G}
    (hB : IsElemAbelian p B) (hx : x ∈ B) (hx1 : x ≠ 1) (h : CentModEqZpowers p B L x) :
    Nat.card ↥(B ⊓ centModSubgroup p L) = p := by
  haveI := Fact.mk hp
  rw [inf_centModSubgroup_eq_zpowers hx h, Nat.card_zpowers]
  exact orderOf_eq_prime (hB.2 x hx) hx1

theorem isDirectZpowersInf_of_cent {B L : Subgroup G} {x : G} (hx : x ∈ B)
    (h : CentModEqZpowers p B L x) (hsup : B = (B ⊓ centModSubgroup p L) ⊔ (B ⊓ L))
    (hinf : (B ⊓ centModSubgroup p L) ⊓ (B ⊓ L) = ⊥) : IsDirectZpowersInf B x L := by
  rw [inf_centModSubgroup_eq_zpowers hx h] at hsup hinf
  exact ⟨hsup, hinf⟩

theorem pRank_eq_of_card (hp : p.Prime) {B : Subgroup G} (hB : IsElemAbelian p B) {k : ℕ}
    (hk : Nat.card B = p ^ k) : CFSG.Open.pRank p B = k :=
  le_antisymm
    (CFSG.SectionRank.pRank_le hp.one_lt fun E hEB _ => hk ▸ Subgroup.card_le_of_le hEB)
    (CFSG.SectionRank.le_pRank hp.one_lt le_rfl hB hk)

theorem glaPLayer_sup_eq (hp : p.Prime) {L B : Subgroup G} (hL : GLAPComponent p L L)
    (hBL : B ≤ Subgroup.normalizer (L : Set G)) (hB : IsPGroup p B) :
    GLAPLayer p (L ⊔ B) = L := by
  set X := L ⊔ B with hX
  have hLX : L ≤ X := le_sup_left
  have hXN : X ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hBL
  haveI hnorm : (L.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLX).2 hXN
  have hsub : IsSubnormal L X := IsSubnormal.step hLX hnorm (IsSubnormal.refl X)
  have hLXc : GLAPComponent p X L := glaPComponent_of_isSubnormal' hp hsub hL
  let π : ↥X →* ↥X ⧸ L.subgroupOf X := QuotientGroup.mk' (L.subgroupOf X)
  have hYp : IsPGroup p (↥X ⧸ L.subgroupOf X) := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have hx : x ∈ (L.subgroupOf X) ⊔ (B.subgroupOf X) := by
      rw [← Subgroup.subgroupOf_sup hLX le_sup_right]
      exact x.2
    obtain ⟨l', hl', b', hb', rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hx
    obtain ⟨n, hn⟩ := hB ⟨(b' : G), Subgroup.mem_subgroupOf.1 hb'⟩
    refine ⟨n, ?_⟩
    have h1 : (QuotientGroup.mk (l' * b') : ↥X ⧸ L.subgroupOf X) = QuotientGroup.mk b' := by
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff l').2 hl', one_mul]
    rw [h1, ← QuotientGroup.mk_pow]
    have h2 : b' ^ (p ^ n) = 1 := Subtype.ext (by
      have := congrArg Subtype.val hn
      simpa using this)
    rw [h2]
    exact QuotientGroup.mk_one _
  have hJle : ∀ J : Subgroup G, GLAPComponent p X J → J ≤ L := by
    intro J hJ
    have hJX : J ≤ X := hJ.1
    let ρ : ↥J →* ↥X ⧸ L.subgroupOf X := π.comp (Subgroup.inclusion hJX)
    haveI : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.2 (glaPComponent_perfect hJ)
    haveI : Group.IsPerfect ↥ρ.range := Group.IsPerfect.range ρ
    haveI := Fact.mk hp
    have hnil : Group.IsNilpotent ↥ρ.range := (hYp.to_subgroup ρ.range).isNilpotent
    have hsub1 : Subsingleton ↥ρ.range := by
      by_contra h
      rw [not_subsingleton_iff_nontrivial] at h
      exact Group.IsPerfect.not_isNilpotent ↥ρ.range hnil
    intro j hj
    have h1 : ρ ⟨j, hj⟩ = 1 := by
      have := Subsingleton.elim (⟨ρ ⟨j, hj⟩, ⟨_, rfl⟩⟩ : ↥ρ.range) 1
      exact congrArg Subtype.val this
    have h2 : (⟨j, hJX hj⟩ : ↥X) ∈ L.subgroupOf X := (QuotientGroup.eq_one_iff _).1 h1
    exact Subgroup.mem_subgroupOf.1 h2
  exact le_antisymm (sSup_le fun J hJ => hJle J hJ) (le_sSup hLXc)

end L6364

end CFSG.LocalAnalysis.GLTheoremA
