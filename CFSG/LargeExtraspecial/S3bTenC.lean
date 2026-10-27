module

public import CFSG.LargeExtraspecial.S3bTenB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith
  CFSG.RankThree.OrthogonalInvolutions OrthoF2

namespace Setting

variable {G : Type*} [Group G] [Finite G] (S : Setting G)

theorem ne_top_of_forall_q_eq_zero {W : Submodule (ZMod 2) S.Qt} (hW : ∀ w ∈ W, S.q w = 0)
    {v : S.Qt} (hv : v ≠ 0) : W ≠ ⊤ := by
  intro htop
  apply hv
  refine S.q_nondegenerate.1 v fun w => ?_
  rw [polarBilin_apply_apply]
  exact polar_eq_zero_of_forall_eq_zero hW (htop ▸ Submodule.mem_top) (htop ▸ Submodule.mem_top)

theorem isReducible_of_commute {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z)
    (hP8 : ∀ h ∈ S.M, g * S.z * g⁻¹ * ((h * g) * S.z * (h * g)⁻¹) =
      (h * g) * S.z * (h * g)⁻¹ * (g * S.z * g⁻¹) → (h * g) * S.z * (h * g)⁻¹ ∈ S.Qa g)
    {h : G} (hh : h ∈ S.M)
    (hab : g * S.z * g⁻¹ * ((h * g) * S.z * (h * g)⁻¹) =
      (h * g) * S.z * (h * g)⁻¹ * (g * S.z * g⁻¹))
    (hba : (h * g) * S.z * (h * g)⁻¹ ≠ g * S.z * g⁻¹)
    (hbaz : (h * g) * S.z * (h * g)⁻¹ ≠ g * S.z * g⁻¹ * S.z) : S.IsReducible := by
  set a := g * S.z * g⁻¹ with ha
  set b := (h * g) * S.z * (h * g)⁻¹ with hb
  have hP8' : ∀ h₁ ∈ S.M, ∀ h₂ ∈ S.M,
      (h₁ * g) * S.z * (h₁ * g)⁻¹ * ((h₂ * g) * S.z * (h₂ * g)⁻¹) =
        (h₂ * g) * S.z * (h₂ * g)⁻¹ * ((h₁ * g) * S.z * (h₁ * g)⁻¹) →
      (h₂ * g) * S.z * (h₂ * g)⁻¹ ∈ S.Qa (h₁ * g) := by
    intro h₁ hh₁ h₂ hh₂ hc
    rw [S.mem_Qa_mul_iff]
    have hm : h₁⁻¹ * h₂ ∈ S.M := S.M.mul_mem (S.M.inv_mem hh₁) hh₂
    have e1 : h₁⁻¹ * ((h₂ * g) * S.z * (h₂ * g)⁻¹) * h₁ =
        (h₁⁻¹ * h₂ * g) * S.z * (h₁⁻¹ * h₂ * g)⁻¹ := by group
    rw [e1]
    refine hP8 _ hm ?_
    calc g * S.z * g⁻¹ * ((h₁⁻¹ * h₂ * g) * S.z * (h₁⁻¹ * h₂ * g)⁻¹) =
          h₁⁻¹ * ((h₁ * g) * S.z * (h₁ * g)⁻¹ * ((h₂ * g) * S.z * (h₂ * g)⁻¹)) * h₁ := by group
      _ = h₁⁻¹ * ((h₂ * g) * S.z * (h₂ * g)⁻¹ * ((h₁ * g) * S.z * (h₁ * g)⁻¹)) * h₁ := by rw [hc]
      _ = (h₁⁻¹ * h₂ * g) * S.z * (h₁⁻¹ * h₂ * g)⁻¹ * (g * S.z * g⁻¹) := by group
  have hbQ : b ∈ S.QG := S.conj_mul_mem_QG hh haQ
  have hbz : b ≠ S.z := S.conj_mul_ne_z hh hne
  have hbQa : b ∈ S.Qa g := hP8 h hh hab
  have haQb : a ∈ S.Qa (h * g) := S.mem_Qa_symm hba hbQa
  have haa : a * a = 1 := (S.conjBy g).z_mul_z
  have hbb : b * b = 1 := (S.conjBy (h * g)).z_mul_z
  set T := S.conjBy g with hT
  have hTz : T.z = a := rfl
  have hgt : h * T.z * h⁻¹ = b := by rw [hTz, hb, ha]; group
  have heQt : S.z ∈ T.Qa h := by
    rw [hT, S.Qa_conjBy]
    exact S.z_mem_Qa hbQ hbz
  have he : S.z ∉ closure ({b, T.z} : Set G) := by
    rw [hTz, mem_closure_pair_iff hbb haa hab.symm]
    rintro (h1 | h1 | h1 | h1)
    · exact S.z_ne_one h1
    · exact hbz h1.symm
    · exact hne h1.symm
    · apply hbaz
      calc b = S.z * a⁻¹ := by rw [h1]; group
        _ = a * S.z := by rw [inv_eq_of_mul_eq_one_right haa, S.z_comm_QG haQ]
  have hab' : b * T.z ≠ b := by
    intro h1
    apply (S.conjBy g).z_ne_one
    calc (S.conjBy g).z = b⁻¹ * (b * T.z) := by rw [hT]; group
      _ = 1 := by rw [h1]; group
  obtain ⟨u, hu, hu1, -⟩ := T.lemma_3_8_2 hgt hbQa (by rw [hTz]; exact hba)
    (S.z_mem_Qa haQ hne) heQt he (b * T.z) (by simp) b (by simp) hab'
  have huM : u ∈ S.M := S.mem_M_iff.mpr (mem_centralizer_singleton_iff.mp hu.2)
  have hba_eq : (u * g) * S.z * (u * g)⁻¹ = b * a := by
    rw [← hTz, ← hu1, hTz, ha]
    group
  have hbaQ : b * a ∈ S.QG := S.QG.mul_mem hbQ haQ
  have hbaz' : b * a ≠ S.z := fun h1 => hbaz (by
    calc b = S.z * a⁻¹ := by rw [← h1]; group
      _ = a * S.z := by rw [inv_eq_of_mul_eq_one_right haa, S.z_comm_QG haQ])
  have hbaQa : b * a ∈ S.Qa g := (S.Qa g).mul_mem hbQa (S.conj_z_mem_Qa g)
  have hbaQb : b * a ∈ S.Qa (h * g) := (S.Qa (h * g)).mul_mem (S.conj_z_mem_Qa (h * g)) haQb
  have ha1 : a ≠ 1 := (S.conjBy g).z_ne_one
  have hb1 : b ≠ 1 := (S.conjBy (h * g)).z_ne_one
  have haQba : a ∈ S.Qa (u * g) := S.mem_Qa_symm (by
    rw [hba_eq]
    intro h1
    apply hb1
    calc b = b * a * a⁻¹ := by group
      _ = 1 := by rw [h1, mul_inv_cancel]) (by rw [hba_eq]; exact hbaQa)
  have hbQba : b ∈ S.Qa (u * g) := S.mem_Qa_symm (by
    rw [hba_eq]
    intro h1
    apply ha1
    calc a = b⁻¹ * (b * a) := by group
      _ = 1 := by rw [h1, inv_mul_cancel]) (by rw [hba_eq]; exact hbaQb)
  have hcomm : ∀ m ∈ S.M, a * ((m * g) * S.z * (m * g)⁻¹) =
      (m * g) * S.z * (m * g)⁻¹ * a ∧ b * ((m * g) * S.z * (m * g)⁻¹) =
      (m * g) * S.z * (m * g)⁻¹ * b := by
    intro m hm
    set c := (m * g) * S.z * (m * g)⁻¹ with hc
    have hcQ : c ∈ S.QG := S.conj_mul_mem_QG hm haQ
    have hcases : c ∈ S.Qa g ∨ c ∈ S.Qa (h * g) ∨ c ∈ S.Qa (u * g) := by
      by_cases h1 : a * c = c * a
      · exact Or.inl (hP8 m hm h1)
      by_cases h2 : b * c = c * b
      · exact Or.inr (Or.inl (hP8' h hh m hm h2))
      · refine Or.inr (Or.inr (hP8' u huM m hm ?_))
        rw [hba_eq]
        have e1 := (S.mul_comm_or haQ hcQ).resolve_left h1
        have e2 := (S.mul_comm_or hbQ hcQ).resolve_left h2
        calc b * a * c = b * (S.z * (c * a)) := by rw [mul_assoc, e1]
          _ = S.z * (b * c) * a := by rw [← mul_assoc b S.z, S.z_comm_QG hbQ]; group
          _ = S.z * (S.z * (c * b)) * a := by rw [e2]
          _ = c * (b * a) := by rw [← mul_assoc S.z S.z, S.z_mul_z, one_mul]; group
    rcases hcases with h1 | h1 | h1
    · exact ⟨S.QG_inf_Qa_comm hne ⟨haQ, S.conj_z_mem_Qa g⟩ ⟨hcQ, h1⟩,
        S.QG_inf_Qa_comm hne ⟨hbQ, hbQa⟩ ⟨hcQ, h1⟩⟩
    · exact ⟨S.QG_inf_Qa_comm hbz ⟨haQ, haQb⟩ ⟨hcQ, h1⟩,
        S.QG_inf_Qa_comm hbz ⟨hbQ, S.conj_z_mem_Qa (h * g)⟩ ⟨hcQ, h1⟩⟩
    · have hbaz'' : (u * g) * S.z * (u * g)⁻¹ ≠ S.z := by rw [hba_eq]; exact hbaz'
      exact ⟨S.QG_inf_Qa_comm hbaz'' ⟨haQ, haQba⟩ ⟨hcQ, h1⟩,
        S.QG_inf_Qa_comm hbaz'' ⟨hbQ, hbQba⟩ ⟨hcQ, h1⟩⟩
  set W : Submodule (ZMod 2) S.Qt := ⨅ m : S.M, S.clSub (S.QG ⊓ S.Qa ((m : G) * g)) with hW
  have haW : S.cl a ∈ W := by
    rw [hW, Submodule.mem_iInf]
    intro m
    have h1 := hP8' m m.2 1 S.M.one_mem (by simpa using (hcomm m m.2).1.symm)
    simp only [one_mul] at h1
    exact S.cl_mem_clSub ⟨haQ, h1⟩ haQ
  refine ⟨W, fun hbot => S.cl_conj_z_ne_zero haQ hne (by rw [hbot] at haW; exact haW),
    S.ne_top_of_forall_q_eq_zero (fun w hw => ?_) (S.cl_conj_z_ne_zero haQ hne), ?_⟩
  · rw [hW, Submodule.mem_iInf] at hw
    have := hw 1
    simp only [OneMemClass.coe_one, one_mul] at this
    exact S.q_eq_zero_of_mem_clSub_QG_inf_Qa hne this
  · intro m₀ v hv
    rw [hW, Submodule.mem_iInf] at hv ⊢
    intro m
    have h1 := hv (m₀⁻¹ * m)
    obtain ⟨w, hw, hwQ, rfl⟩ := S.mem_clSub_iff.mp h1
    rw [S.ρ_cl m₀ hwQ]
    refine S.cl_mem_clSub ⟨S.conj_mem_QG m₀.2 hwQ, ?_⟩ (S.conj_mem_QG m₀.2 hwQ)
    have := S.conj_mem_Qa_mul (h := (m₀ : G)) hw.2
    simpa [mul_assoc] using this

theorem Lbar_inf_eq_bot {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hP9 : ∀ h ∈ S.M, g * S.z * g⁻¹ * ((h * g) * S.z * (h * g)⁻¹) =
      (h * g) * S.z * (h * g)⁻¹ * (g * S.z * g⁻¹) →
      (h * g) * S.z * (h * g)⁻¹ = g * S.z * g⁻¹ ∨
        (h * g) * S.z * (h * g)⁻¹ = g * S.z * g⁻¹ * S.z)
    {h : G} (hh : h ∈ S.M) (hL : S.Lbar (h * g) ≠ S.Lbar g) :
    S.Lbar g ⊓ S.Lbar (h * g) = ⊥ := by
  set a := g * S.z * g⁻¹ with ha
  set b := (h * g) * S.z * (h * g)⁻¹ with hb
  have hbQ : b ∈ S.QG := S.conj_mul_mem_QG hh haQ
  have hbz : b ≠ S.z := S.conj_mul_ne_z hh hne
  have hab : a * b ≠ b * a := by
    intro h1
    rcases hP9 h hh h1 with h2 | h2
    · exact hL (S.Lbar_eq_of_conj_eq h2)
    · exact hL (S.Lbar_eq_of_conj_eq_mul_z haQ hne h2)
  have hab' : a * b = S.z * (b * a) := (S.mul_comm_or haQ hbQ).resolve_left hab
  have haba : a * b * a⁻¹ = b * S.z := by
    rw [hab', show S.z * (b * a) * a⁻¹ = S.z * b by group, ← S.z_comm_QG hbQ]
  have hbab : b * a * b⁻¹ = a * S.z := by
    have e : b * a = S.z * (a * b) := by
      rw [hab', ← mul_assoc S.z S.z, S.z_mul_z, one_mul]
    rw [e, show S.z * (a * b) * b⁻¹ = S.z * a by group, ← S.z_comm_QG haQ]
  rw [eq_bot_iff]
  intro s hs
  rw [Subgroup.mem_bot]
  by_contra hs1
  obtain ⟨⟨t, htM⟩, ht, rfl⟩ := S.mem_Lbar_iff.mp hs.1
  have htQ : t ∉ S.QG := fun h1 => hs1 ((S.ρ_eq_one_iff _).mpr h1)
  have htb : t * b * t⁻¹ = b ∨ t * b * t⁻¹ = b * S.z := by
    have h1 := S.mem_fixLbar.mp (S.cl_mem_fixLbar_self hbQ) _ hs.2
    rw [S.ρ_cl _ hbQ] at h1
    exact (S.cl_eq_cl_iff hbQ (S.conj_mem_QG htM hbQ)).mp h1.symm
  obtain ⟨t', ht'L, ht'Q, ht'b⟩ : ∃ t' ∈ S.L0 g, t' ∉ S.QG ∧ t' * b = b * t' := by
    rcases htb with h1 | h1
    · refine ⟨t, ht, htQ, ?_⟩
      calc t * b = t * b * t⁻¹ * t := by group
        _ = b * t := by rw [h1]
    · refine ⟨t * a, mul_mem ht ⟨S.conj_z_mem_Qa g, S.QG_le_M haQ⟩, fun hm => htQ ?_, ?_⟩
      · have := S.QG.mul_mem hm (S.QG.inv_mem haQ)
        rwa [mul_inv_cancel_right] at this
      · have e : t * a * b * (t * a)⁻¹ = b := by
          calc t * a * b * (t * a)⁻¹ = t * (a * b * a⁻¹) * t⁻¹ := by group
            _ = t * b * t⁻¹ * (t * S.z * t⁻¹) := by rw [haba]; group
            _ = b := by rw [h1, S.conj_z_of_mem_M htM, mul_assoc, S.z_mul_z, mul_one]
        calc t * a * b = t * a * b * (t * a)⁻¹ * (t * a) := by group
          _ = b * (t * a) := by rw [e]
  set T := S.conjBy g with hT
  have hTz : T.z = a := rfl
  have ht'Qaz : t' ∈ T.Qa b := by
    rw [hT, S.Qa_conjBy]
    have := S.conj_mem_Qa_mul (h := b) ht'L.1
    rwa [show b * t' * b⁻¹ = t' by rw [← ht'b]; group] at this
  have htQ' : b * T.z * b⁻¹ ∈ T.QG := by
    rw [hTz, hbab]
    exact (S.Qa g).mul_mem (S.conj_z_mem_Qa g) (S.z_mem_Qa haQ hne)
  have htne : b * T.z * b⁻¹ ≠ T.z := by
    rw [hTz, hbab]
    intro h1
    exact S.z_ne_one (by simpa using h1)
  have he : t' ∉ closure ({b * T.z * b⁻¹, T.z} : Set G) := by
    intro hm
    apply ht'Q
    have hle : closure ({b * T.z * b⁻¹, T.z} : Set G) ≤ S.QG := by
      rw [closure_le]
      rintro _ (rfl | rfl)
      · rw [hTz, hbab]
        exact S.QG.mul_mem haQ S.z_mem_QG
      · exact haQ
    exact hle hm
  have hdist : T.z ≠ b * T.z * b⁻¹ * T.z := by
    rw [hTz, hbab]
    intro h1
    exact hne (h1.trans (S.mul_z_mul_self haQ (S.conjBy g).z_mul_z))
  obtain ⟨u, hu, -, hu2⟩ := T.lemma_3_8_2 rfl htQ' htne ht'L.1 ht'Qaz he T.z (by simp)
    (b * T.z * b⁻¹ * T.z) (by simp) hdist
  have hux : u * t' * u⁻¹ = t' := by
    rw [mem_centralizer_singleton_iff.mp hu.2]
    group
  have hz : (u * (b * g)) * S.z * (u * (b * g))⁻¹ = S.z := by
    calc (u * (b * g)) * S.z * (u * (b * g))⁻¹ = u * (b * T.z * b⁻¹) * u⁻¹ := by
          rw [hTz, ha]; group
      _ = b * T.z * b⁻¹ * T.z := hu2
      _ = S.z := by
          rw [hTz, hbab]
          exact S.mul_z_mul_self haQ (S.conjBy g).z_mul_z
  have hmem := S.conj_mem_Qa_mul (h := u) (show t' ∈ S.Qa (b * g) by
    rw [← S.Qa_conjBy]
    exact ht'Qaz)
  rw [hux, ← mul_assoc, S.Qa_eq_QG_of_conj_eq (by rw [mul_assoc u b g]; exact hz)] at hmem
  exact ht'Q hmem

end Setting

end CFSG.LargeExtraspecial
