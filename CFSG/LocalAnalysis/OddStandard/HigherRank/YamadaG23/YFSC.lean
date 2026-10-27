module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YFQ8
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YFGen
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YFR

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} (s : Setting3 G L)

private lemma conjSub_mul {G : Type} [Group G] (a b : G) (Y : Subgroup G) :
    conjSub (a * b) Y = conjSub a (conjSub b Y) := by
  unfold conjSub
  rw [Subgroup.map_map (g := (MulAut.conj a).toMonoidHom) (f := (MulAut.conj b).toMonoidHom)]
  congr 1
  ext x
  change MulAut.conj (a * b) x = MulAut.conj a (MulAut.conj b x)
  rw [MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply]
  group

private lemma mem_normalizer_iff_conjSub_eq {G : Type} [Group G] {H : Subgroup G} {g : G} :
    g ∈ normalizer (H : Set G) ↔ conjSub g H = H := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  rfl

private lemma frame_Sσ_eq_sup {Γ : Type} [Group Γ] (fr : Frame Γ) :
    fr.Sσ = fr.S ⊔ closure ({fr.σ} : Set Γ) := by
  rw [Frame.Sσ, SFrame.S, ← Subgroup.closure_union]
  congr 1
  ext x
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false,
    or_false, false_or]
  tauto

private lemma zpow_two_eq_one_or_self {Γ : Type} [Group Γ] {x : Γ} (hx : x ^ 2 = 1) (k : ℤ) :
    x ^ k = 1 ∨ x ^ k = x := by
  have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · left
    rw [orderOf_eq_one_iff.mp h1, one_zpow]
  · have hmod := zpow_mod_orderOf x k
    rw [h2] at hmod
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · left
      rw [← hmod, show k % ((2 : ℕ) : ℤ) = 0 from by simpa using h0]
      simp
    · right
      rw [← hmod, show k % ((2 : ℕ) : ℤ) = 1 from by simpa using h1]
      simp

private lemma mem_sup_closure_or {Γ : Type} [Group Γ] {S : Subgroup Γ} {σ : Γ}
    (hσ : σ ^ 2 = 1) (hnorm : ∀ s ∈ S, σ * s * σ⁻¹ ∈ S) :
    ∀ x ∈ S ⊔ closure ({σ} : Set Γ), x ∈ S ∨ ∃ s ∈ S, x = s * σ := by
  have hσ2 : σ * σ = 1 := by rw [← pow_two]; exact hσ
  intro x hx
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction (p := fun x _ => x ∈ S ∨ ∃ s ∈ S, x = s * σ)
    ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with hyS | hyσ
    · exact Or.inl hyS
    · rw [← Subgroup.zpowers_eq_closure] at hyσ
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hyσ
      rcases zpow_two_eq_one_or_self hσ k with h1 | hσ'
      · exact Or.inl (by rw [← hk, h1]; exact S.one_mem)
      · exact Or.inr ⟨1, S.one_mem, by rw [← hk, hσ', one_mul]⟩
  · exact Or.inl S.one_mem
  · intro y z _ _ hy hz
    rcases hy with hyS | ⟨a, haS, rfl⟩
    · rcases hz with hzS | ⟨b, hbS, rfl⟩
      · exact Or.inl (S.mul_mem hyS hzS)
      · exact Or.inr ⟨y * b, S.mul_mem hyS hbS, by rw [mul_assoc]⟩
    · rcases hz with hzS | ⟨b, hbS, rfl⟩
      · refine Or.inr ⟨a * (σ * z * σ⁻¹), S.mul_mem haS (hnorm z hzS), ?_⟩
        group
      · refine Or.inl ?_
        have h2 : σ * b * σ⁻¹ ∈ S := hnorm b hbS
        have heq : (a * σ) * (b * σ) = a * (σ * b * σ⁻¹) * (σ * σ) := by group
        rw [heq, hσ2, mul_one]
        exact S.mul_mem haS h2
  · intro y _ hy
    rcases hy with hyS | ⟨a, haS, rfl⟩
    · exact Or.inl (S.inv_mem hyS)
    · refine Or.inr ⟨σ * a⁻¹ * σ⁻¹, hnorm a⁻¹ (S.inv_mem haS), ?_⟩
      calc (a * σ)⁻¹ = σ⁻¹ * a⁻¹ := mul_inv_rev a σ
        _ = σ * a⁻¹ := by rw [inv_eq_of_mul_eq_one_right hσ2]
        _ = (σ * a⁻¹ * σ⁻¹) * σ := by
              rw [show (σ * a⁻¹ * σ⁻¹) * σ = σ * a⁻¹ * (σ⁻¹ * σ) by group,
                inv_mul_cancel, mul_one]

theorem s3_R1_RneT (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (hOut : (innerAut (L ⧸ center L)).index = 2) (h31 : s.Fact31) (hA : LFactsA s)
    (e : Setting3.Ext s) (hRT : s.R ≠ s.T)
    (hAN : ∀ x ∈ e.T₁, ∀ y ∈ s.fr.A, x * y * x⁻¹ ∈ s.fr.A) :
    e.R₁ ⊓ s.T = s.R ∧ e.R₁.relIndex e.T₁ = 2 := by
  classical
  set U : Subgroup G := closure {s.fr.a₁, s.fr.b₁} with hU
  set V : Subgroup G := closure {s.fr.a₂, s.fr.b₂} with hV
  have hR1 : e.R₁ = normIn e.T₁ U := by
    unfold Setting3.Ext.R₁
    rw [if_neg hRT, ← hU]
  rw [hR1]
  have hU_le_A : U ≤ s.fr.A := by
    apply Subgroup.closure_mono
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto
  have hUV : U ≠ V := by
    have h := s3_U_ne_V hS hZ s
    rwa [← hU, ← hV] at h
  have ht_cen : s.t ∈ Subgroup.centralizer (U : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact s3_comm_t_of_mem_A s (hU_le_A ha)
  have htN : conjSub s.t U = U :=
    mem_normalizer_iff_conjSub_eq.mp (Subgroup.centralizer_le_normalizer (U : Set G) ht_cen)
  have hNA : ∀ x ∈ e.T₁, x ∈ normalizer (s.fr.A : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro a
    exact ⟨hAN x hx a, fun ha => by
      have hmem := hAN x⁻¹ (e.T₁.inv_mem hx) (x * a * x⁻¹) ha
      rwa [show x⁻¹ * (x * a * x⁻¹) * (x⁻¹)⁻¹ = a by group] at hmem⟩
  have hpermb : ∀ x ∈ e.T₁,
      (conjSub x U = U ∧ conjSub x V = V) ∨ (conjSub x U = V ∧ conjSub x V = U) := by
    intro x hx
    have h := s3_Q8_perm hS hZ s (hNA x hx)
    rwa [← hU, ← hV] at h
  have hmem_R1 : ∀ x : G, x ∈ normIn e.T₁ U ↔ x ∈ e.T₁ ∧ conjSub x U = U := by
    intro x
    rw [normIn, Subgroup.mem_inf, mem_normalizer_iff_conjSub_eq]
  have hS_NU : s.fr.S ≤ normalizer (U : Set G) := srel_S_le_normalizer_U (s3_srel hS hZ s)
  have hR_le_R1 : s.R ≤ normIn e.T₁ U := by
    intro r hr
    rw [hmem_R1 r]
    refine ⟨e.T_le (s.R_le_T hr), ?_⟩
    obtain ⟨y, hyS, hy | hy⟩ := s3_R_cases s hS h31 r hr
    · rw [hy]
      exact mem_normalizer_iff_conjSub_eq.mp (hS_NU hyS)
    · rw [hy, conjSub_mul y s.t U, htN]
      exact mem_normalizer_iff_conjSub_eq.mp (hS_NU hyS)
  have hle_R : normIn e.T₁ U ⊓ s.T ≤ s.R := by
    intro y hy
    rw [Subgroup.mem_inf] at hy
    obtain ⟨hyR1, hyT⟩ := hy
    obtain ⟨-, hyU⟩ := (hmem_R1 y).mp hyR1
    by_contra hyR
    haveI : Group.IsPerfect ↥L := isPerfect_of_hrSetting hS
    set jy : MulAut (L ⧸ center L) := jOn L (s3_T_le_N s hS) ⟨y, hyT⟩ with hjy
    have hy_acts : ActsAs L y jy := by
      rw [hjy]
      exact jOn_actsAs L (s3_T_le_N s hS) ⟨y, hyT⟩
    have hjy_Sσ : jy ∈ s.fr'.Sσ := by
      rw [← s3_jSub_T s hS hOut hRT, ← range_jOn L (s3_T_le_N s hS)]
      exact MonoidHom.mem_range.mpr ⟨⟨y, hyT⟩, by rw [hjy]⟩
    by_cases hjyS : jy ∈ s.fr'.S
    · have hjyR : jy ∈ jSub L s.R := by rwa [s3_jSub_R s]
      obtain ⟨r, hrR, hr_acts⟩ := (mem_jSub L).mp hjyR
      have htriv : ActsAs L (r⁻¹ * y) 1 := by
        have h := actsAs_mul L (actsAs_inv L hr_acts) hy_acts
        rwa [inv_mul_cancel] at h
      have hmemT : r⁻¹ * y ∈ s.T := s.T.mul_mem (s.T.inv_mem (s.R_le_T hrR)) hyT
      have hcen : r⁻¹ * y ∈ centralizer (L : Set G) := (actsAs_one_iff L).mp htriv
      have hzp : r⁻¹ * y ∈ zpowers s.t := by
        rw [← s3_T_inf_centralizer s h31]
        exact Subgroup.mem_inf.mpr ⟨hmemT, hcen⟩
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzp
      exact hyR (by
        have htR : s.t ^ k ∈ s.R := s.R.zpow_mem (s3_t_mem_R s) k
        rw [hk] at htR
        have hmul := s.R.mul_mem hrR htR
        rwa [mul_inv_cancel_left] at hmul)
    · have hnormσ : ∀ a ∈ s.fr'.S, s.fr'.σ * a * s.fr'.σ⁻¹ ∈ s.fr'.S :=
        fun a ha =>
          (Subgroup.mem_normalizer_iff.mp (frame_sigma_normalizes s.fr' s.facts.1) a).mp ha
      have hjy_dec : jy ∈ s.fr'.S ∨ ∃ p ∈ s.fr'.S, jy = p * s.fr'.σ := by
        refine mem_sup_closure_or (hσ := frame_sigma_sq s.fr' s.facts.1) hnormσ jy ?_
        rwa [← frame_Sσ_eq_sup s.fr']
      rcases hjy_dec with hjyS' | ⟨p, hpS, hp_eq⟩
      · exact absurd hjyS' hjyS
      · obtain ⟨-, g, hgT, -, hgActs, -⟩ := fusionDef_aut s hS h31 hOut hRT
        have hp_jS : p ∈ jSub L s.fr.S := by rw [s3_jSub_S s]; exact hpS
        obtain ⟨r, hrS, hr_acts⟩ := (mem_jSub L).mp hp_jS
        have hjy_eq : jy = p * s.fr'.σ := hp_eq
        have h_acts_rg : ActsAs L (r * g) (p * s.fr'.σ) := actsAs_mul L hr_acts hgActs
        have htriv : ActsAs L ((r * g)⁻¹ * y) 1 := by
          have h := actsAs_mul L (actsAs_inv L h_acts_rg) hy_acts
          rw [hjy_eq, inv_mul_cancel] at h
          exact h
        have hmemT : (r * g)⁻¹ * y ∈ s.T :=
          s.T.mul_mem (s.T.inv_mem (s.T.mul_mem (s3_S_le_T s hrS) hgT)) hyT
        have hcen : (r * g)⁻¹ * y ∈ centralizer (L : Set G) := (actsAs_one_iff L).mp htriv
        have hzp : (r * g)⁻¹ * y ∈ zpowers s.t := by
          rw [← s3_T_inf_centralizer s h31]
          exact Subgroup.mem_inf.mpr ⟨hmemT, hcen⟩
        obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hzp
        have hy_eq : y = (r * g) * s.t ^ m := by rw [hm]; group
        have htmN : s.t ^ m ∈ normalizer (U : Set G) :=
          Subgroup.centralizer_le_normalizer (U : Set G)
            ((Subgroup.centralizer (U : Set G)).zpow_mem ht_cen m)
        have htmU : conjSub (s.t ^ m) U = U := mem_normalizer_iff_conjSub_eq.mp htmN
        have hrU : conjSub r U = U := mem_normalizer_iff_conjSub_eq.mp (hS_NU hrS)
        have hgU : conjSub g U = V := s3_swap hS hZ s hgT hgActs
        have hconj : conjSub y U = conjSub r V := by
          rw [hy_eq, conjSub_mul (r * g) (s.t ^ m) U,
            conjSub_mul r g (conjSub (s.t ^ m) U), htmU, hgU]
        have hne : conjSub r V ≠ U := by
          have hinj : Function.Injective (Subgroup.map (MulAut.conj r).toMonoidHom) :=
            Subgroup.map_injective (MulAut.conj r).injective
          have hne' : conjSub r V ≠ conjSub r U := hinj.ne (fun h => hUV h.symm)
          rwa [hrU] at hne'
        rw [hconj] at hyU
        exact hne hyU
  refine ⟨le_antisymm hle_R (le_inf hR_le_R1 s.R_le_T), ?_⟩
  rw [Subgroup.relIndex_eq_two_iff]
  obtain ⟨-, g, hgT, -, hgActs, -⟩ := fusionDef_aut s hS h31 hOut hRT
  have hgT1 : g ∈ e.T₁ := e.T_le hgT
  have hgU : conjSub g U = V := s3_swap hS hZ s hgT hgActs
  refine ⟨g, hgT1, fun b hb => ?_⟩
  have hbR1 : ∀ x ∈ e.T₁, (x ∈ normIn e.T₁ U ↔ conjSub x U = U) := by
    intro x hx
    rw [hmem_R1 x]
    exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩
  rcases hpermb b hb with ⟨hbU, hbV⟩ | ⟨hbU, hbV⟩
  · have hbg_eq : conjSub (b * g) U = V := by rw [conjSub_mul b g U, hgU, hbV]
    refine Or.inr ⟨(hbR1 b hb).mpr hbU, ?_⟩
    rw [hbR1 (b * g) (e.T₁.mul_mem hb hgT1), hbg_eq]
    exact fun h => hUV h.symm
  · have hb_notin : b ∉ normIn e.T₁ U := by
      rw [hbR1 b hb]
      exact fun h => hUV (hbU.symm.trans h).symm
    have hbg_in : b * g ∈ normIn e.T₁ U := by
      rw [hbR1 (b * g) (e.T₁.mul_mem hb hgT1), conjSub_mul b g U, hgU, hbV]
    exact Or.inl ⟨hbg_in, hb_notin⟩

end CFSG.OddStandard.HigherRank.YamadaG23
