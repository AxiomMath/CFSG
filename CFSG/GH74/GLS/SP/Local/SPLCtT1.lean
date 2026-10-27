module

public import CFSG.GH74.GLS.SP.Local.SPLCt0

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

section CtT1

theorem exists_maximal_two_subgroup {G : Type} [Group G] [Finite G] (X P : Subgroup G)
    (hPX : P ≤ X) (hP : IsPGroup 2 P) :
    ∃ T : Subgroup G, P ≤ T ∧ T ≤ X ∧ IsPGroup 2 T ∧
      ∀ Q : Subgroup G, Q ≤ X → IsPGroup 2 Q → T ≤ Q → Q = T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := (IsPGroup.comap_subtype hP (K := X)).exists_le_sylow
  refine ⟨(Q : Subgroup ↥X).map X.subtype, ?_, Subgroup.map_subtype_le _, Q.isPGroup'.map _, ?_⟩
  · intro x hx
    exact ⟨⟨x, hPX hx⟩, hQ hx, rfl⟩
  · intro Q' hQ'X hQ'p hle
    have hmax : Q'.subgroupOf X = (Q : Subgroup ↥X) := by
      apply Q.is_maximal' (IsPGroup.comap_subtype hQ'p)
      intro q hq
      exact hle ⟨q, hq, rfl⟩
    apply le_antisymm
    · intro x hx
      have : (⟨x, hQ'X hx⟩ : ↥X) ∈ Q'.subgroupOf X := hx
      rw [hmax] at this
      exact ⟨_, this, rfl⟩
    · exact hle

theorem isPGroup_two_sup_of_comm {G : Type} [Group G] {A B : Subgroup G}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hA : IsPGroup 2 ↥A) (hB : IsPGroup 2 ↥B) :
    IsPGroup 2 ↥(A ⊔ B) :=
  hA.to_sup_of_normal_right' hB fun a ha =>
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun b hb => (hc a ha b hb).symm)

theorem sup_decomp_of_le_normalizer {G : Type} [Group G] {N H : Subgroup G}
    (h : H ≤ normalizer (N : Set G)) {g : G} (hg : g ∈ N ⊔ H) : ∃ n ∈ N, ∃ k ∈ H, g = n * k := by
  have hset := Subgroup.coe_mul_of_right_le_normalizer_left N H h
  have hg' : g ∈ (↑(N ⊔ H) : Set G) := hg
  rw [hset] at hg'
  obtain ⟨n, hn, k, hk, hnk⟩ := Set.mem_mul.mp hg'
  exact ⟨n, hn, k, hk, hnk.symm⟩

theorem pow_mul_mem_aux {G : Type} [Group G] (I F : Subgroup G)
    (hnorm : ∀ f ∈ F, ∀ i ∈ I, f * i * f⁻¹ ∈ I) {i f : G} (hi : i ∈ I) (hf : f ∈ F) (k : ℕ) :
    ∃ i' ∈ I, (i * f) ^ k = i' * f ^ k := by
  induction k with
  | zero => exact ⟨1, I.one_mem, by simp⟩
  | succ k ih =>
    obtain ⟨i', hi', hk⟩ := ih
    refine ⟨i' * (f ^ k * i * (f ^ k)⁻¹), I.mul_mem hi' (hnorm _ (F.pow_mem hf k) i hi), ?_⟩
    rw [pow_succ, hk, pow_succ]
    group

theorem mem_of_two_element {G : Type} [Group G] [Finite G] (I F T : Subgroup G)
    (hnorm : ∀ f ∈ F, ∀ i ∈ I, f * i * f⁻¹ ∈ I) (hodd : Odd (Nat.card ↥F)) (hT : IsPGroup 2 T)
    {i f : G} (hi : i ∈ I) (hf : f ∈ F) (hw : i * f ∈ T) : i * f ∈ I := by
  have hfm : f ^ Nat.card ↥F = 1 := by
    have h := pow_card_eq_one' (G := ↥F) (x := ⟨f, hf⟩)
    exact congrArg Subtype.val h
  obtain ⟨i', hi', hk⟩ := pow_mul_mem_aux I F hnorm hi hf (Nat.card ↥F)
  have hwm : (i * f) ^ Nat.card ↥F ∈ I := by rw [hk, hfm, mul_one]; exact hi'
  obtain ⟨k, hk2⟩ := hT ⟨i * f, hw⟩
  have hwk : (i * f) ^ (2 ^ k) = 1 := congrArg Subtype.val hk2
  have hcop : Nat.Coprime (orderOf (i * f)) (Nat.card ↥F) :=
    Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hwk)
      (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd))
  have hord : orderOf ((i * f) ^ Nat.card ↥F) = orderOf (i * f) := hcop.orderOf_pow
  have hle : zpowers ((i * f) ^ Nat.card ↥F) ≤ zpowers (i * f) :=
    zpowers_le.mpr (Subgroup.pow_mem _ (mem_zpowers _) _)
  have heq : zpowers ((i * f) ^ Nat.card ↥F) = zpowers (i * f) := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [Nat.card_zpowers, Nat.card_zpowers, hord]
  have : i * f ∈ zpowers ((i * f) ^ Nat.card ↥F) := by rw [heq]; exact mem_zpowers _
  exact (zpowers_le.mpr hwm) this

variable {G : Type} [Group G] [Finite G] (D : SPLNot1 G)

omit [Finite G] in
theorem zt_comm_CCt {b : G} (hb : b ∈ D.C ⊓ D.Ct) :
    ∀ a ∈ zpowers D.z ⊔ zpowers D.t, a * b = b * a := by
  have hbz : b * D.z = D.z * b := mem_centralizer_singleton_iff.mp hb.1
  have hbt : b * D.t = D.t * b := mem_centralizer_singleton_iff.mp hb.2
  have : zpowers D.z ⊔ zpowers D.t ≤ centralizer ({b} : Set G) :=
    sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hbz.symm))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hbt.symm))
  intro a ha
  exact mem_centralizer_singleton_iff.mp (this ha)

theorem zt_isPGroup (hs : SPLSetup D.toSPLNot0) : IsPGroup 2 ↥(zpowers D.z ⊔ zpowers D.t) := by
  have hzt := z_comm_t' D hs
  have hzp : IsPGroup 2 ↥(zpowers D.z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs.syl.z_inv]; simp)
  have htp : IsPGroup 2 ↥(zpowers D.t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs.syl.t_ord]; simp)
  refine isPGroup_two_sup_of_comm ?_ hzp htp
  intro a ha b hb
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hb
  exact (Commute.zpow_zpow (show Commute D.z D.t from hzt) i j).eq

theorem ctT_pre (hs : SPLSetup D.toSPLNot0) :
    ∃ T T₁ : Subgroup G, T ≤ D.Ct ∧ IsPGroup 2 ↥T ∧
      (∀ P : Subgroup G, P ≤ D.Ct → IsPGroup 2 ↥P → T ≤ P → P = T) ∧
      zpowers D.z ⊔ zpowers D.t ≤ T ∧ T₁ = T ⊓ D.Ict ∧ T₁ ≤ D.S₁ ∧
      IVK.IsDihedralOrder ↥T₁ (2 ^ (D.n - 1)) ∧
      D.C ⊓ T = (zpowers D.z ⊔ zpowers D.t) ⊔ T₁ := by
  obtain ⟨T₁, hT₁le, hT₁p, hT₁max, hT₁dih⟩ := (splCt0 D hs).T₁ex
  have hT₁I : T₁ ≤ D.Ict := hT₁le.trans inf_le_left
  have hT₁S : T₁ ≤ D.S₁ := hT₁le.trans inf_le_right
  have hztp := zt_isPGroup D hs
  have hcI : ∀ a ∈ zpowers D.z ⊔ zpowers D.t, ∀ b ∈ T₁, a * b = b * a := fun a ha b hb =>
    zt_comm_CCt D (Ict_le_CCt D hs (hT₁I hb)) a ha
  have hPp : IsPGroup 2 ↥((zpowers D.z ⊔ zpowers D.t) ⊔ T₁) :=
    isPGroup_two_sup_of_comm hcI hztp hT₁p
  have hztCt : zpowers D.z ⊔ zpowers D.t ≤ D.Ct :=
    sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (z_comm_t' D hs)))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))
  have hPle : (zpowers D.z ⊔ zpowers D.t) ⊔ T₁ ≤ D.Ct :=
    sup_le hztCt (hT₁I.trans (Ict_le_Ct D hs))
  obtain ⟨T, hPT, hTle, hTp, hTmax⟩ := exists_maximal_two_subgroup D.Ct _ hPle hPp
  have hztT : zpowers D.z ⊔ zpowers D.t ≤ T := le_trans le_sup_left hPT
  have hT₁T : T₁ ≤ T := le_trans le_sup_right hPT
  have hT₁eq : T₁ = T ⊓ D.Ict :=
    (hT₁max (T ⊓ D.Ict) inf_le_right (IsPGroup.to_le hTp inf_le_left)
      (le_inf hT₁T hT₁I)).symm
  refine ⟨T, T₁, hTle, hTp, hTmax, hztT, hT₁eq, hT₁S, hT₁dih, ?_⟩
  apply le_antisymm
  · rintro c ⟨hcC, hcT⟩
    have hcM : c ∈ D.C ⊓ D.Ct := ⟨hcC, hTle hcT⟩
    rw [CCt_eq D hs] at hcM
    have hcomm : ∀ a ∈ zpowers D.z ⊔ zpowers D.t, ∀ b ∈ D.Ict ⊔ D.F₀, a * b = b * a := by
      intro a ha b hb
      have hbM : b ∈ D.C ⊓ D.Ct := by
        rw [CCt_eq D hs]; exact Subgroup.mem_sup_right hb
      exact zt_comm_CCt D hbM a ha
    obtain ⟨a, ha, w, hw, hcw⟩ := mem_sup_of_commute hcomm hcM
    have hcw' : c = a * w := hcw
    have haT : a ∈ T := hztT ha
    have hwT : w ∈ T := by
      have : w = a⁻¹ * c := by rw [hcw']; group
      rw [this]; exact T.mul_mem (T.inv_mem haT) hcT
    obtain ⟨i, hi, f, hf, hwif⟩ := sup_decomp_of_le_normalizer (F₀_le_normalizer_I D hs) hw
    rw [hwif] at hwT
    have hiI : i * f ∈ D.Ict :=
      mem_of_two_element D.Ict D.F₀ T (F₀_norm D hs) (F₀_odd D) hTp hi hf hwT
    have hw1 : w ∈ T₁ := by rw [hT₁eq, hwif]; exact ⟨hwT, hiI⟩
    rw [hcw']
    exact Subgroup.mul_mem_sup ha hw1
  · refine sup_le (sup_le ?_ ?_) ?_
    · rw [zpowers_le]
      exact ⟨mem_centralizer_singleton_iff.mpr rfl, hztT (Subgroup.mem_sup_left (mem_zpowers _))⟩
    · rw [zpowers_le]
      exact ⟨mem_centralizer_singleton_iff.mpr (z_comm_t' D hs).symm,
        hztT (Subgroup.mem_sup_right (mem_zpowers _))⟩
    · exact le_inf ((hT₁I.trans (Ict_le_K D hs)).trans (K_le_C D.ext3 hs)) hT₁T

end CtT1

end CFSG.GH74.GLS.SP.Local
