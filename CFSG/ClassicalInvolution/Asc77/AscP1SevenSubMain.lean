module

public import CFSG.ClassicalInvolution.Asc77.AscP1SevenSubStab
public import CFSG.ClassicalInvolution.Asc77.AscP1SevenSubGrp
public import CFSG.ClassicalInvolution.Asc77.AscP1SevenGraph

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77.Thompson

namespace Thompson

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

omit [Finite G] [Fact p.Prime] in
theorem muGroup_comm_iff {q q' : ↥(muGroup Ω W)} :
    q * q' = q' * q ↔ (q : NQuot (W ⊔ OCW W)) * q' = q' * q :=
  ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem exists_perm_four_of_wv (c : Ctx p f Ω W) (hTT : Star3T.IsTT (muDelta Ω W))
    (hS : Star3T.IsStar (muDelta Ω W)) {R₁ R₂ : Subgroup G} (hR₁ : R₁ ∈ DSet Ω W)
    (hR₂ : R₂ ∈ DSet Ω W) (hDC : DComm W R₁ R₂) {r₁ : G} (hr₁ : r₁ ∈ R₁) (hr₁W : r₁ ∉ W)
    {d a : ↥(muGroup Ω W)} (hd : (d : NQuot (W ⊔ OCW W)) = piG W r₁)
    (hdΔ : d ∈ muDelta Ω W) (haΔ : a ∈ muDelta Ω W) (hconn : ¬ Star3T.Conn (muDelta Ω W) d a)
    (hk : (Star3T.cent (muDelta Ω W) d).ncard = 4) {w v : G} (hw : w ∈ R₁ ⊓ W)
    (hv : v ∈ R₂ ⊓ W) (hw4 : orderOf w = 4) (hv4 : orderOf v = 4) :
    ∃ ψ : ↥(Subgroup.closure (muDeltaCent Ω W (w * v))) ≃* Equiv.Perm (Fin 4),
      ∀ (x : ↥(muGroup Ω W)) (hx : x ∈ Subgroup.closure (muDeltaCent Ω W (w * v))),
        x ∈ muDeltaCent Ω W (w * v) ↔ (ψ ⟨x, hx⟩).IsSwap := by
  classical
  have hp := c.hp
  have hq := c.hq
  have hΩ := c.hΩ
  have he : w * v ∈ W := W.mul_mem hw.2 hv.2
  have he' : w⁻¹ * v ∈ W := W.mul_mem (W.inv_mem hw.2) hv.2
  obtain ⟨K₁, hK₁, hR₁K⟩ := exists_isSylow2In_of_mem_RSet hR₁.1
  obtain ⟨K₂, hK₂, hR₂K⟩ := exists_isSylow2In_of_mem_RSet hR₂.1
  obtain ⟨r₂, hr₂, hr₂W⟩ := c.exists_not_mem_W hR₂ hK₂ hR₂K
  let ρ₁ : Rep Ω W := ⟨K₁, R₁, r₁, hK₁, hR₁, hR₁K, hr₁, hr₁W⟩
  let ρ₂ : Rep Ω W := ⟨K₂, R₂, r₂, hK₂, hR₂, hR₂K, hr₂, hr₂W⟩
  obtain ⟨x₂, hx₂⟩ : ∃ x₂ : ↥(muGroup Ω W), (x₂ : NQuot (W ⊔ OCW W)) = piG W r₂ :=
    ⟨⟨piG W r₂, piG_mem_muGroup (Subgroup.mem_sup_left (le_MGrp_of_mem_D hR₂ hr₂))⟩, rfl⟩
  have hx₂Δ : x₂ ∈ muDelta Ω W := ⟨R₂, hR₂, r₂, hr₂, hr₂W, hx₂⟩
  have hcomm12 : ρ₁.img * ρ₂.img = ρ₂.img * ρ₁.img :=
    (piG_comm_iff (hR₁.2 hr₁) (hR₂.2 hr₂)).mpr (hDC.2 r₁ hr₁ r₂ hr₂)
  have hK12 : K₁ ≠ K₂ := by
    intro h
    exact hDC.1 (c.hkey R₁ hR₁ R₂ hR₂ K₁ hK₁ hR₁K.1 (h ▸ hR₂K.1))
  have hΩ12 : K₂ ∈ omegaNbr Ω K₁ := c.omega_of_comm ρ₁ ρ₂ hK12 hcomm12
  have hΩ21 : K₁ ∈ omegaNbr Ω K₂ := c.omega_of_comm ρ₂ ρ₁ hK12.symm hcomm12.symm
  have hwK : w ∈ K₁ ⊓ W := ⟨hR₁K.1 hw.1, hw.2⟩
  have hvK : v ∈ K₂ ⊓ W := ⟨hR₂K.1 hv.1, hv.2⟩
  obtain ⟨z₁, hz₁⟩ := hΩ.exists_uniqueInvolution hp hq hK₁
  obtain ⟨z₂, hz₂⟩ := hΩ.exists_uniqueInvolution hp hq hK₂
  have hw2 : w * w = z₁ := sq_eq_involution_of_orderOf_four hz₁ hwK.1 hw4
  have hv2 : v * v = z₂ := sq_eq_involution_of_orderOf_four hz₂ hvK.1 hv4
  have f1 : r₁ * w * r₁⁻¹ = w⁻¹ := c.conj_inv ρ₁ hwK
  have f2 : r₁ * v * r₁⁻¹ = v := by
    rw [mul_inv_eq_iff_eq_mul]
    exact c.centralizes ρ₁ ρ₂ hΩ12 hvK
  have f3 : r₂ * w * r₂⁻¹ = w := by
    rw [mul_inv_eq_iff_eq_mul]
    exact c.centralizes ρ₂ ρ₁ hΩ21 hwK
  have f4 : r₂ * v * r₂⁻¹ = v⁻¹ := c.conj_inv ρ₂ hvK
  have g1 : r₁ * (w * v) * r₁⁻¹ = w⁻¹ * v := by
    calc r₁ * (w * v) * r₁⁻¹ = (r₁ * w * r₁⁻¹) * (r₁ * v * r₁⁻¹) := by group
      _ = w⁻¹ * v := by rw [f1, f2]
  have g1' : r₁ * (w⁻¹ * v) * r₁⁻¹ = w * v := by
    calc r₁ * (w⁻¹ * v) * r₁⁻¹ = (r₁ * w * r₁⁻¹)⁻¹ * (r₁ * v * r₁⁻¹) := by group
      _ = w * v := by rw [f1, f2, inv_inv]
  have g2 : r₂ * (w * v) * r₂⁻¹ = w * v⁻¹ := by
    calc r₂ * (w * v) * r₂⁻¹ = (r₂ * w * r₂⁻¹) * (r₂ * v * r₂⁻¹) := by group
      _ = w * v⁻¹ := by rw [f3, f4]
  have hz₁ne : z₁ ≠ 1 := hz₁.ne_one
  have hz₂ne : z₂ ≠ 1 := hz₂.ne_one
  have n1 : w⁻¹ * v ≠ w * v := by
    intro h
    have h' : w⁻¹ = w := mul_right_cancel h
    apply hz₁ne
    rw [← hw2]
    calc w * w = w⁻¹ * w := by rw [h']
      _ = 1 := inv_mul_cancel w
  have n2 : w * v⁻¹ ≠ w * v := by
    intro h
    have h' : v⁻¹ = v := mul_left_cancel h
    apply hz₂ne
    rw [← hv2]
    calc v * v = v⁻¹ * v := by rw [h']
      _ = 1 := inv_mul_cancel v
  have hd₂ne : d ≠ x₂ := by
    intro h
    apply hK12
    refine c.K_eq_of_img_eq ρ₁ ρ₂ ?_
    have h' : (d : NQuot (W ⊔ OCW W)) = x₂ := congrArg Subtype.val h
    rw [hd, hx₂] at h'
    exact h'
  have hcommdx₂ : x₂ * d = d * x₂ := by
    rw [muGroup_comm_iff, hx₂, hd]
    exact hcomm12.symm
  have hx₂F : x₂ ∈ Star3T.cent (muDelta Ω W) d := ⟨hx₂Δ, hcommdx₂⟩
  have hdF : d ∈ Star3T.cent (muDelta Ω W) d := Star3T.self_mem_cent hdΔ
  have hFeq : ∀ z ∈ Star3T.cent (muDelta Ω W) d,
      Star3T.cent (muDelta Ω W) z = Star3T.cent (muDelta Ω W) d := fun z hz =>
    Star3T.cent_eq_of_mem_cent hTT hS hdΔ haΔ hconn hz
  have hΛ : ∀ y, y ∈ muDeltaCent Ω W (w * v) ↔ y ∈ muDelta Ω W ∧ y ∈ muStab Ω W (w * v) :=
    fun y => by rw [c.muDeltaCent_eq_inter he]; exact Iff.rfl
  have hd_not : d ∉ muStab Ω W (w * v) := by
    intro h
    have := (c.mem_muStab_iff he hR₁ hr₁ hd).mp h
    exact n1 (g1.symm.trans this)
  have hx₂_not : x₂ ∉ muStab Ω W (w * v) := by
    intro h
    have := (c.mem_muStab_iff he hR₂ hr₂ hx₂).mp h
    exact n2 (g2.symm.trans this)
  have hFstab : ∀ q ∈ Star3T.cent (muDelta Ω W) d, q ≠ d → q ≠ x₂ →
      q ∈ muStab Ω W (w * v) := by
    intro q hqF hqd hqx
    obtain ⟨ρ, hρ⟩ := exists_rep_of_mem_muDelta hqF.1
    have hqx₂ : q * x₂ = x₂ * q := by
      have : q ∈ Star3T.cent (muDelta Ω W) x₂ := by rw [hFeq x₂ hx₂F]; exact hqF
      exact this.2
    have hcd : ρ.img * ρ₁.img = ρ₁.img * ρ.img := by
      have h' := muGroup_comm_iff.mp hqF.2
      rw [hd, ← hρ] at h'
      exact h'
    have hcx : ρ.img * ρ₂.img = ρ₂.img * ρ.img := by
      have h' := muGroup_comm_iff.mp hqx₂
      rw [hx₂, ← hρ] at h'
      exact h'
    have hKne1 : ρ.K ≠ K₁ := fun h =>
      hqd (Subtype.ext (hρ.symm.trans ((c.img_eq_of_K_eq ρ ρ₁ h).trans hd.symm)))
    have hKne2 : ρ.K ≠ K₂ := fun h =>
      hqx (Subtype.ext (hρ.symm.trans ((c.img_eq_of_K_eq ρ ρ₂ h).trans hx₂.symm)))
    have e1 : ρ.r * w * ρ.r⁻¹ = w := by
      rw [mul_inv_eq_iff_eq_mul]
      exact c.centralizes ρ ρ₁ (c.omega_of_comm ρ ρ₁ hKne1 hcd) hwK
    have e2 : ρ.r * v * ρ.r⁻¹ = v := by
      rw [mul_inv_eq_iff_eq_mul]
      exact c.centralizes ρ ρ₂ (c.omega_of_comm ρ ρ₂ hKne2 hcx) hvK
    refine (c.mem_muStab_iff he ρ.hR ρ.hr hρ.symm).mpr ?_
    calc ρ.r * (w * v) * ρ.r⁻¹ = (ρ.r * w * ρ.r⁻¹) * (ρ.r * v * ρ.r⁻¹) := by group
      _ = w * v := by rw [e1, e2]
  have hAstab : ∀ q ∈ muDelta Ω W, q ∉ Star3T.cent (muDelta Ω W) d →
      q ∈ muStab Ω W (w * v) ∨ q ∈ muStab Ω W (w⁻¹ * v) := by
    intro q hqΔ hqF
    obtain ⟨ρ, hρ⟩ := exists_rep_of_mem_muDelta hqΔ
    have hKne1 : ρ.K ≠ K₁ := fun h => hqF (by
      have : q = d := Subtype.ext (hρ.symm.trans ((c.img_eq_of_K_eq ρ ρ₁ h).trans hd.symm))
      rw [this]
      exact hdF)
    have hKne2 : ρ.K ≠ K₂ := fun h => hqF (by
      have : q = x₂ := Subtype.ext (hρ.symm.trans ((c.img_eq_of_K_eq ρ ρ₂ h).trans hx₂.symm))
      rw [this]
      exact hx₂F)
    have hnot1 : K₁ ∉ omegaNbr Ω ρ.K := fun h => hqF (by
      have h' := c.comm_of_omega ρ ρ₁ h
      refine ⟨hqΔ, muGroup_comm_iff.mpr ?_⟩
      rw [hd, ← hρ]
      exact h')
    have hnot2 : K₂ ∉ omegaNbr Ω ρ.K := fun h => hqF (by
      have h' := c.comm_of_omega ρ ρ₂ h
      have : q ∈ Star3T.cent (muDelta Ω W) x₂ :=
        ⟨hqΔ, muGroup_comm_iff.mpr (by rw [hx₂, ← hρ]; exact h')⟩
      rwa [hFeq x₂ hx₂F] at this)
    obtain ⟨z, hz⟩ := hΩ.exists_uniqueInvolution hp hq ρ.hK
    rcases c.stab_dichotomy ρ ρ₁ ρ₂ hKne1 hKne2 hnot1 hnot2 hwK hvK hz hz₁ hz₂ hw2 hv2 with
      h | h
    · exact Or.inl ((c.mem_muStab_iff he ρ.hR ρ.hr hρ.symm).mpr h)
    · exact Or.inr ((c.mem_muStab_iff he' ρ.hR ρ.hr hρ.symm).mpr h)
  have haF : a ∉ Star3T.cent (muDelta Ω W) d := fun h => hconn (Star3T.conn_of_mem_cent hdΔ h)
  have hdd : d * d = 1 := hTT.mul_self d hdΔ
  obtain ⟨a', ha'Δ, ha'S, ha'F⟩ : ∃ a' ∈ muDelta Ω W, a' ∈ muStab Ω W (w * v) ∧
      a' ∉ Star3T.cent (muDelta Ω W) d := by
    rcases hAstab a haΔ haF with h | h
    · exact ⟨a, haΔ, h, haF⟩
    · refine ⟨d * a * d, hTT.mul_mul_mem hdΔ haΔ, ?_, ?_⟩
      · obtain ⟨n, hnN, hn, hne⟩ := h
        have hr₁N := hR₁.2 hr₁
        have hinv₁ : (piG W r₁)⁻¹ = piG W r₁ :=
          inv_eq_of_mul_eq_one_left (piG_mul_self_of_mem_D hp hq hΩ c.hW hR₁ hr₁)
        refine ⟨r₁ * n * r₁⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _ hr₁N hnN)
          (Subgroup.inv_mem _ hr₁N), ?_, ?_⟩
        · rw [Subgroup.coe_mul, Subgroup.coe_mul,
            piG_mul (Subgroup.mul_mem _ hr₁N hnN) (Subgroup.inv_mem _ hr₁N), piG_mul hr₁N hnN,
            piG_inv hr₁N, hinv₁, hd, hn]
        · have hr1inv : r₁⁻¹ * (w * v) * r₁ = w⁻¹ * v := by
            calc r₁⁻¹ * (w * v) * r₁ = r₁⁻¹ * (r₁ * (w⁻¹ * v) * r₁⁻¹) * r₁ := by rw [g1']
              _ = w⁻¹ * v := by group
          calc (r₁ * n * r₁⁻¹) * (w * v) * (r₁ * n * r₁⁻¹)⁻¹
              = r₁ * (n * (r₁⁻¹ * (w * v) * r₁) * n⁻¹) * r₁⁻¹ := by group
            _ = r₁ * (n * (w⁻¹ * v) * n⁻¹) * r₁⁻¹ := by rw [hr1inv]
            _ = r₁ * (w⁻¹ * v) * r₁⁻¹ := by rw [hne]
            _ = w * v := g1'
      · intro h'
        apply haF
        refine ⟨haΔ, ?_⟩
        have h2 := h'.2
        calc a * d = d * (d * a * d) := by
              calc a * d = (d * d) * a * d := by rw [hdd, one_mul]
                _ = d * (d * a * d) := by simp only [mul_assoc]
          _ = (d * a * d) * d := h2.symm
          _ = d * a := by
              calc (d * a * d) * d = d * a * (d * d) := by simp only [mul_assoc]
                _ = d * a := by rw [hdd, mul_one]
  have hsub : ({d, x₂} : Set ↥(muGroup Ω W)) ⊆ Star3T.cent (muDelta Ω W) d := by
    intro y hy
    rcases hy with h | h
    · rw [h]; exact hdF
    · rw [Set.mem_singleton_iff.mp h]; exact hx₂F
  have hcard2 : (Star3T.cent (muDelta Ω W) d \ {d, x₂}).ncard = 2 := by
    rw [Set.ncard_sdiff hsub, hk, Set.ncard_pair hd₂ne]
  obtain ⟨d₃, d₄, hd₃₄, hset⟩ := Set.ncard_eq_two.mp hcard2
  have hd₃ : d₃ ∈ Star3T.cent (muDelta Ω W) d \ {d, x₂} := by rw [hset]; exact Or.inl rfl
  have hd₄ : d₄ ∈ Star3T.cent (muDelta Ω W) d \ {d, x₂} := by rw [hset]; exact Or.inr rfl
  have hne3 : d₃ ≠ d ∧ d₃ ≠ x₂ := ⟨fun h => hd₃.2 (Or.inl h), fun h => hd₃.2 (Or.inr h)⟩
  have hne4 : d₄ ≠ d ∧ d₄ ≠ x₂ := ⟨fun h => hd₄.2 (Or.inl h), fun h => hd₄.2 (Or.inr h)⟩
  have hΛF : ∀ y, y ∈ muDeltaCent Ω W (w * v) → y ∈ Star3T.cent (muDelta Ω W) d →
      y = d₃ ∨ y = d₄ := by
    intro y hyΛ hyF
    have hyS := ((hΛ y).mp hyΛ).2
    have hyd : y ≠ d := fun h => hd_not (h ▸ hyS)
    have hyx : y ≠ x₂ := fun h => hx₂_not (h ▸ hyS)
    have hy : y ∈ Star3T.cent (muDelta Ω W) d \ {d, x₂} := by
      refine ⟨hyF, ?_⟩
      rintro (h | h)
      · exact hyd h
      · exact hyx h
    rw [hset] at hy
    exact hy
  have hd₃Λ : d₃ ∈ muDeltaCent Ω W (w * v) :=
    (hΛ d₃).mpr ⟨hd₃.1.1, hFstab d₃ hd₃.1 hne3.1 hne3.2⟩
  have hd₄Λ : d₄ ∈ muDeltaCent Ω W (w * v) :=
    (hΛ d₄).mpr ⟨hd₄.1.1, hFstab d₄ hd₄.1 hne4.1 hne4.2⟩
  have ha'Λ : a' ∈ muDeltaCent Ω W (w * v) := (hΛ a').mpr ⟨ha'Δ, ha'S⟩
  have hΛΔ : muDeltaCent Ω W (w * v) ⊆ muDelta Ω W := fun y hy => ((hΛ y).mp hy).1
  have hconj : ∀ g ∈ Subgroup.closure (muDeltaCent Ω W (w * v)),
      ∀ x ∈ muDeltaCent Ω W (w * v), g * x * g⁻¹ ∈ muDeltaCent Ω W (w * v) := by
    have hcl : Subgroup.closure (muDeltaCent Ω W (w * v)) ≤ muStab Ω W (w * v) :=
      (Subgroup.closure_le _).mpr fun y hy => ((hΛ y).mp hy).2
    intro g hg x hx
    refine (hΛ _).mpr ⟨hTT.conj_mem' (hΛΔ hx) g, ?_⟩
    exact (muStab Ω W (w * v)).mul_mem ((muStab Ω W (w * v)).mul_mem (hcl hg) ((hΛ x).mp hx).2)
      ((muStab Ω W (w * v)).inv_mem (hcl hg))
  have hconnΛ : ∀ y, Star3T.Conn (muDeltaCent Ω W (w * v)) d₃ y → y = d₃ ∨ y = d₄ := by
    intro y hy
    induction hy with
    | refl => exact Or.inl rfl
    | @tail b y' _ hbc ih =>
      have hbF : b ∈ Star3T.cent (muDelta Ω W) d := by
        rcases ih with h | h
        · rw [h]; exact hd₃.1
        · rw [h]; exact hd₄.1
      have hy'F : y' ∈ Star3T.cent (muDelta Ω W) d := by
        have : y' ∈ Star3T.cent (muDelta Ω W) b := ⟨hΛΔ hbc.2.1, hbc.2.2.symm⟩
        rwa [hFeq b hbF] at this
      exact hΛF y' hbc.2.1 hy'F
  have hc : ¬ Star3T.Conn (muDeltaCent Ω W (w * v)) d₃ a' := fun h => ha'F (by
    rcases hconnΛ a' h with h' | h'
    · rw [h']; exact hd₃.1
    · rw [h']; exact hd₄.1)
  have hcentΛ : Star3T.cent (muDeltaCent Ω W (w * v)) d₃ = {d₃, d₄} := by
    ext y
    constructor
    · rintro ⟨hyΛ, hyc⟩
      have hyF : y ∈ Star3T.cent (muDelta Ω W) d₃ := ⟨hΛΔ hyΛ, hyc⟩
      rw [hFeq d₃ hd₃.1] at hyF
      exact hΛF y hyΛ hyF
    · intro hy
      rcases hy with h | h
      · rw [h]; exact Star3T.self_mem_cent hd₃Λ
      · rw [Set.mem_singleton_iff.mp h]
        exact ⟨hd₄Λ, hTT.isClique_cent hS hdΔ haΔ hconn hd₄.1 hd₃.1⟩
  have hk' : (Star3T.cent (muDeltaCent Ω W (w * v)) d₃).ncard = 2 := by
    rw [hcentΛ]
    exact Set.ncard_pair hd₃₄
  exact Star3T.exists_mulEquiv_perm_four_of_closure hTT hS hΛΔ hconj hd₃Λ ha'Λ hc hk'

end Thompson

end CFSG.ClassicalInvolution.Asc77
