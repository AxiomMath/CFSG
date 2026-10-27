module

public import CFSG.Blueprint.Catalog
public import CFSG.LargeExtraspecial.S3Basic
import CFSG.Adapters.ClassicalCatalogReverse
import CFSG.LargeExtraspecial.AS35WSp4Gen

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Aschbacher1977

open CFSG CFSG.Blueprint CFSG.LargeExtraspecial Subgroup

variable {G : Type} [Group G]

theorem lieModel_PSU_four_two_of_PSp_two_three (h : LieModel G .PSp 2 3 1) :
    LieModel G .PSU 4 2 1 :=
  Or.inl ⟨by decide,
    CFSG.ClassicalModels.statedClassicalModel_PSU_four_two_of_PSp_two_three
      (h.statedClassicalModel (by decide))⟩

theorem lieModel_PSp_two_three_one {p f : ℕ} (hp : p.Prime) (h : LieModel G .PSp 2 p f)
    (h3 : p ^ f = 3) : LieModel G .PSp 2 3 1 := by
  obtain ⟨rfl, rfl⟩ := CFSG.GH74.Generic.eq_three_of_pow_eq_three hp h.admissible.2.1 h3
  exact h

variable [Finite G]

theorem false_of_isSimpleGroup_normal_le_M (S : Setting G) {N : Subgroup G} (hNM : N ≤ S.M)
    (hNn : ∀ c ∈ S.M, ∀ n ∈ N, c * n * c⁻¹ ∈ N) (hs : IsSimpleGroup N)
    (hna : ∃ a b : N, a * b ≠ b * a) : False := by
  set R := S.QG
  have hRN : (R.subgroupOf N).Normal := by
    refine ⟨fun r hr c => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hr ⊢
    simpa using S.conj_mem_QG (hNM c.2) hr
  have := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (R.subgroupOf N) with h1 | h1
  ·
    obtain ⟨a, b, hab⟩ := hna
    have key : ∀ n ∈ N, n = 1 := by
      intro n hn
      have hc : ∀ r ∈ R, n * r = r * n := by
        intro r hr
        have hN' : n * (r * n⁻¹ * r⁻¹) ∈ N :=
          N.mul_mem hn (hNn r (S.QG_le_M hr) n⁻¹ (N.inv_mem hn))
        have hR' : n * r * n⁻¹ * r⁻¹ ∈ R :=
          R.mul_mem (S.conj_mem_QG (hNM hn) hr) (R.inv_mem hr)
        have heq : n * (r * n⁻¹ * r⁻¹) = n * r * n⁻¹ * r⁻¹ := by group
        have hmem : (⟨_, hN'⟩ : N) ∈ R.subgroupOf N := by
          rw [Subgroup.mem_subgroupOf]
          change n * (r * n⁻¹ * r⁻¹) ∈ R
          rw [heq]
          exact hR'
        rw [h1, Subgroup.mem_bot] at hmem
        have h2 : n * r * n⁻¹ * r⁻¹ = 1 := by
          rw [← heq]
          exact congrArg Subtype.val hmem
        calc n * r = n * r * n⁻¹ * r⁻¹ * (r * n) := by group
          _ = r * n := by rw [h2, one_mul]
      have hnR : n ∈ R := S.mem_QG_of_commute (hNM hn) hc
      have : (⟨n, hn⟩ : N) ∈ R.subgroupOf N := hnR
      rw [h1] at this
      exact congrArg Subtype.val ((Subgroup.mem_bot).1 this)
    have ha : a = 1 := Subtype.ext (key _ a.2)
    have hb : b = 1 := Subtype.ext (key _ b.2)
    exact hab (by rw [ha, hb])
  ·
    have hle : N ≤ S.QG := by
      intro n hn
      have : (⟨n, hn⟩ : N) ∈ R.subgroupOf N := by rw [h1]; exact Subgroup.mem_top _
      exact this
    exact AS35W.not_isPGroup_of_simple hs hna (S.isPGroup_QG.to_le hle)

theorem false_of_mulEquiv_isSimpleGroup_normal {P : Type} [Group P] (S : Setting G) (σ : G ≃* P)
    {L : Subgroup P} (hLC : L ≤ centralizer ({σ S.z} : Set P))
    (hLn : ∀ c ∈ centralizer ({σ S.z} : Set P), ∀ l ∈ L, c * l * c⁻¹ ∈ L)
    (hs : IsSimpleGroup L) (hna : ∃ a b : L, a * b ≠ b * a) : False := by
  let N : Subgroup G := L.comap σ.toMonoidHom
  have hNM : N ≤ S.M := by
    intro n hn
    have hσn : σ n ∈ L := Subgroup.mem_comap.mp hn
    refine S.mem_M_iff.mpr (σ.injective ?_)
    rw [map_mul, map_mul]
    exact mem_centralizer_singleton_iff.mp (hLC hσn)
  have hNn : ∀ c ∈ S.M, ∀ n ∈ N, c * n * c⁻¹ ∈ N := by
    intro c hc n hn
    change σ (c * n * c⁻¹) ∈ L
    have hσc : σ c ∈ centralizer ({σ S.z} : Set P) :=
      mem_centralizer_singleton_iff.mpr
        (by simpa [map_mul] using congrArg σ (S.mem_M_iff.mp hc))
    have hσn : σ n ∈ L := Subgroup.mem_comap.mp hn
    simpa [map_mul] using hLn (σ c) hσc (σ n) hσn
  let e : L ≃* N :=
    { toFun := fun l => ⟨σ.symm l, by rw [Subgroup.mem_comap]; simp⟩
      invFun := fun n => ⟨σ n, Subgroup.mem_comap.mp n.2⟩
      left_inv := fun l => Subtype.ext (by simp)
      right_inv := fun n => Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [map_mul]) }
  have hsN : IsSimpleGroup N := e.isSimpleGroup_congr.mp hs
  have hnaN : ∃ a b : N, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hna
    exact ⟨e a, e b, fun h => hab (by simpa using congrArg e.symm h)⟩
  exact false_of_isSimpleGroup_normal_le_M S hNM hNn hsN hnaN

open CFSG.ComponentClassification.CatFactsSp4 CFSG.Open in
theorem not_lieModel_PSp_two_of_ne_three (S : Setting G) (hw : S.width = 2) {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (h : LieModel G .PSp 2 p f) (h3 : p ^ f ≠ 3) :
    False := by
  obtain ⟨-, -, K, _, _, hK, ⟨e⟩⟩ := CFSG.GH74.Generic.lieModel_psp_data h
  have : Finite (StatedProj (StatedSp 2 K)) := Finite.of_equiv G e.toEquiv
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.odd_of_ne_two hp2).pow
  have hK3 : Nat.card K ≠ 3 := by rw [hK]; exact h3
  have hK4 : 4 ≤ Nat.card K := by
    obtain ⟨k, hk⟩ := hodd
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    omega
  obtain ⟨g, hg⟩ := exists_conj_of_orderOf_eq_two hodd (u := e S.z)
    (by rw [MulEquiv.orderOf_eq]; exact S.orderOf_z)
  let σ : G ≃* StatedProj (StatedSp 2 K) := e.trans (MulAut.conj g⁻¹)
  have hσz : σ S.z = g⁻¹ * e S.z * g := by
    show MulAut.conj g⁻¹ (e S.z) = g⁻¹ * e S.z * g
    rw [MulAut.conj_apply, inv_inv]
  rw [← hσz] at hg
  rcases hg with hg | hg
  · have hcard := CFSG.GH74.GLS.IVK.GHInv.card_centralizer_eq_of_mulEquiv σ S.z
    rw [hg] at hcard
    have hdvd1 : Nat.card K ^ 2 ∣
        Nat.card ↥(centralizer ({u1 K} : Set (StatedProj (StatedSp 2 K)))) :=
      (AS35W.sq_dvd_card_X0 hodd).trans (Subgroup.card_dvd_of_le (X0_le_centralizer (K := K)))
    have hdvd2 : Nat.card K ^ 2 ∣ Nat.card S.M := by
      show Nat.card K ^ 2 ∣ Nat.card ↥(centralizer ({S.z} : Set G))
      rw [hcard]
      exact hdvd1
    have hdvd3 : (p ^ f) ^ 2 ∣ 2 ^ 8 * 3 ^ 2 * 5 := by
      rw [← hK]
      exact hdvd2.trans (S.card_M_dvd_of_width_two hw)
    exact h3 (AS35W.eq_three_of_sq_dvd hp hp2 hf hdvd3)
  · have hs : IsSimpleGroup (Lsub K) := isSimpleGroup_Lsub (K := K) hK4
    have hne : Lsub K ≠ ⊥ := by
      have := hs
      exact (Subgroup.nontrivial_iff_ne_bot (Lsub K)).mp inferInstance
    have hna : ∃ a b : Lsub K, a * b ≠ b * a :=
      AS35W.exists_noncomm_of_perfect (AS35W.lsub_perfect (K := K) hK4) hne
    have hLC : Lsub K ≤ centralizer ({σ S.z} : Set (StatedProj (StatedSp 2 K))) := by
      rw [hg]
      exact Lsub_le_centralizer (K := K)
    have hLn : ∀ c ∈ centralizer ({σ S.z} : Set (StatedProj (StatedSp 2 K))),
        ∀ l ∈ Lsub K, c * l * c⁻¹ ∈ Lsub K := by
      intro c hc l hl
      rw [hg] at hc
      exact AS35W.conj_mem_Lsub (K := K) hodd hK4 hc hl
    exact false_of_mulEquiv_isSimpleGroup_normal S σ hLC hLn hs hna

end CFSG.GF2Type.Aschbacher1977
