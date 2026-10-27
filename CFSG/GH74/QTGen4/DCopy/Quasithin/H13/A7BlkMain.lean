module

public import CFSG.Quasithin.H13.A7BlkMain
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S136e
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1622t
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5X1367d

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open CFSG.Quasithin.H13.A7Blk Equiv Equiv.Perm

theorem lem13622A7Block_of_F4
    (h1222 : Stmt12_2_2_F4) (h517 : Stmt5_1_7_one_F4) : Lem13622A7Block_F4 := by
  intro G _ _ T L V S _ K _ hY hTN hLvK _ hblk hAT
  have hshort : IsShort2 K := hblk.1
  obtain ⟨D₀⟩ := nonempty_altData hAT
  set Gv := Subgroup.centralizer ({S.v12} : Set G) with hGv
  have hKG : K ≤ Gv := hY.1
  have hsylGv := S.isSylowTwoOf_Tv_F4 h1222 h517
  have hsylX : IsSylowTwoOf S.Tv (K ⊔ S.Tv) :=
    A4.isSylowTwoOf_mono hsylGv le_sup_right (sup_le hKG inf_le_right)
  have hsylK : IsSylowTwoOf (S.Tv ⊓ K) K :=
    A4.isSylowTwoOf_inf_normal hsylX le_sup_left (sup_le Subgroup.le_normalizer hTN)
  obtain ⟨D, hD⟩ := exists_stdPos D₀ hTN hsylGv.2.1 hsylK

  have hfix6 : ∀ (t : G) (ht : t ∈ S.Tv), D.act ⟨t, hTN ht⟩ 6 = 6 := by
    obtain ⟨i, hi⟩ := exists_fixed D.α D.surj D.ker (by norm_num) (by norm_num) (by decide) hTN
      hsylGv.2.1
    have hi6 : i = 6 := by
      refine eq_six_of_fix fun p hp => ?_
      obtain ⟨k, hkT, rfl⟩ := hD.pstd_le p hp
      have h1 := hi k hkT
      rwa [show (⟨(k : G), hTN hkT⟩ : ↥(Subgroup.normalizer (K : Set G))) =
        ⟨(k : G), Subgroup.le_normalizer k.2⟩ from rfl, act_of_mem] at h1
    intro t ht
    rw [← hi6]
    exact hi t ht
  have hTK₁ : S.Tv ≤ Subgroup.normalizer (ptCore D.α 6 : Set G) := fun t ht =>
    mem_normalizer_ptCore D.α D.surj D.ker (by norm_num) (by norm_num) (hTN ht) (hfix6 t ht)
  refine ⟨ptCore D.α 6, ptCore_le D.α 6, mem_lFamily_ptCore D.α D.surj D.ker (by norm_num) hTK₁,
    hTK₁, ?_, nonempty_quot_ptCore D.α D.surj D.ker (by norm_num) 6⟩

  set Λ : Subgroup (Perm (Fin 7)) :=
    (S.Lv.subgroupOf K).map ((alternatingGroup (Fin 7)).subtype.comp D.α) with hΛ
  have hnorm : ∀ c : ↥K, (c : G) ∈ Subgroup.normalizer (S.Lv : Set G) →
      ∀ μ ∈ Λ, (D.α c : Perm (Fin 7)) * μ * (D.α c : Perm (Fin 7))⁻¹ ∈ Λ := by
    intro c hc μ hμ
    obtain ⟨l, hl, rfl⟩ := hμ
    refine ⟨c * l * c⁻¹, ?_, ?_⟩
    · have hl' : (l : G) ∈ S.Lv := hl
      show ((c * l * c⁻¹ : ↥K) : G) ∈ S.Lv
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact (Subgroup.mem_normalizer_iff.mp hc _).mp hl'
    · simp only [MonoidHom.coe_comp, Function.comp_apply, map_mul, map_inv, Subgroup.coe_subtype]
  have hgen : ∀ n ∈ pstd, ∃ c : ↥K, (c : G) ∈ Subgroup.normalizer (S.Lv : Set G) ∧
      (D.α c : Perm (Fin 7)) = n := by
    intro n hn
    obtain ⟨k, hkT, hk⟩ := hD.pstd_le n hn
    exact ⟨k, S.Tv_le_normalizer_Lv hkT, hk⟩
  have hpi3 : ∃ c : ↥K, (c : G) ∈ Subgroup.normalizer (S.Lv : Set G) ∧
      (D.α c : Perm (Fin 7)) = pi3 := by
    obtain ⟨k, hk, hkB⟩ := hD.exists_mem_normalizer_baum hshort
    have hkB' : (k : G) ∈ Gv ⊓ Subgroup.normalizer (baum T : Set G) := by
      refine ⟨hKG k.2, ?_⟩
      rw [← S.lemma_13_6_4.1]
      exact hkB
    have hkM := S.lemma_13_6_5_F4 h1222 h517 hkB'
    exact ⟨k, S.mem_normalizer_Lv hkM.1 hkM.2, hk⟩
  have hΛfix : ∀ μ ∈ Λ, μ 6 = 6 := by
    by_contra hne
    simp only [not_forall] at hne
    obtain ⟨μ₀, hμ₀, hμ₀6⟩ := hne
    classical
    set s : Finset (Fin 7) := Finset.univ.filter fun x => ∃ μ ∈ Λ, μ 6 = x with hs
    have hmem : ∀ x, x ∈ s ↔ ∃ μ ∈ Λ, μ 6 = x := fun x => by simp [hs]
    have hclosed : ∀ c : ↥K, (c : G) ∈ Subgroup.normalizer (S.Lv : Set G) →
        (D.α c : Perm (Fin 7)) 6 = 6 → ∀ x ∈ s, (D.α c : Perm (Fin 7)) x ∈ s := by
      intro c hc hc6 x hx
      rw [hmem] at hx ⊢
      obtain ⟨μ, hμ, rfl⟩ := hx
      refine ⟨_, hnorm c hc μ hμ, ?_⟩
      have hinv : (D.α c : Perm (Fin 7))⁻¹ 6 = 6 := by rw [Perm.inv_eq_iff_eq, hc6]
      rw [Perm.mul_apply, Perm.mul_apply, hinv]
    have hcl : ∀ n : Perm (Fin 7), (∃ c : ↥K, (c : G) ∈ Subgroup.normalizer (S.Lv : Set G) ∧
        (D.α c : Perm (Fin 7)) = n) → n 6 = 6 → ∀ x ∈ s, n x ∈ s := by
      rintro n ⟨c, hc, rfl⟩ hn6
      exact hclosed c hc hn6
    have huniv := eq_univ_of_closed s ((hmem 6).mpr ⟨1, Λ.one_mem, rfl⟩)
      ⟨μ₀ 6, (hmem _).mpr ⟨μ₀, hμ₀, rfl⟩, hμ₀6⟩ (hcl n1 (hgen n1 n1_mem) n1_six)
      (hcl n2 (hgen n2 n2_mem) n2_six) (hcl n3 (hgen n3 n3_mem) n3_six) (hcl pi3 hpi3 pi3_six)

    have horb : MulAction.orbit Λ (6 : Fin 7) = Set.univ := by
      ext x
      simp only [Set.mem_univ, iff_true]
      have hx : x ∈ s := by rw [huniv]; exact Finset.mem_univ x
      obtain ⟨μ, hμ, rfl⟩ := (hmem x).mp hx
      exact ⟨⟨μ, hμ⟩, rfl⟩
    have h7 : 7 ∣ Nat.card Λ := by
      have h1 := MulAction.index_stabilizer Λ (6 : Fin 7)
      rw [horb, Set.ncard_univ, Nat.card_fin] at h1
      have h2 := Subgroup.index_dvd_card (MulAction.stabilizer (↥Λ) (6 : Fin 7))
      rwa [h1] at h2
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    have := Fintype.ofFinite ↥Λ
    rw [Nat.card_eq_fintype_card] at h7
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card 7 h7
    obtain ⟨l, hl, hlx⟩ := x.2
    obtain ⟨k, hk⟩ := S.exists_pow_eq_one_of_mem_Lv (Subgroup.mem_subgroupOf.mp hl)
    have hlk : l ^ (3 * 2 ^ k) = 1 := Subtype.ext (by simpa using hk)
    have hxk : x ^ (3 * 2 ^ k) = 1 := by
      apply Subtype.ext
      rw [SubgroupClass.coe_pow, ← hlx, ← map_pow, hlk, map_one]
      rfl
    have hdvd := orderOf_dvd_of_pow_eq_one hxk
    rw [hx] at hdvd
    rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).mp hdvd with h | h
    · exact absurd h (by decide)
    · exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 7) h) (by decide)
  show oTwoRes (L ⊓ Gv) ≤ ptCore D.α 6
  refine oTwoRes_le_ptCore D.α D.surj D.ker (by norm_num) hLvK fun x hx => ?_
  exact hΛfix _ ⟨⟨x, hLvK hx⟩, hx, rfl⟩

end CFSG.Quasithin.H13.A5

end
