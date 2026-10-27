module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP12c
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbTSub
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC0C

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private lemma comm_of_mem_W (hc : Ctx4 t L S x₁ x₂ lam rho tau) {a b : G}
    (ha : a ∈ ctxW t x₁ x₂) (hb : b ∈ ctxW t x₁ x₂) : a * b = b * a := by
  haveI := hc.abelian_W
  exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥(ctxW t x₁ x₂)) ⟨b, hb⟩)

private lemma mem_zpowers_eq_one_or_eq {a x : G} (ha : a * a = 1)
    (hx : x ∈ Subgroup.zpowers a) : x = 1 ∨ x = a := by
  rw [Subgroup.zpowers_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
      rw [Set.mem_singleton_iff] at hy
      exact Or.inr hy
  | one => exact Or.inl rfl
  | mul y z _ _ hy hz =>
      rcases hy with hy | hy <;> rcases hz with hz | hz
      · left; rw [hy, hz, one_mul]
      · right; rw [hy, hz, one_mul]
      · right; rw [hy, hz, mul_one]
      · left; rw [hy, hz, ha]
  | inv y _ hy =>
      rcases hy with hy | hy
      · left; rw [hy, inv_one]
      · right; rw [hy, mul_eq_one_iff_inv_eq.mp ha]

private lemma tau_conj_baseGrp (hc : Ctx4 t L S x₁ x₂ lam rho tau) {b : G}
    (hb : b ∈ baseGrp x₁ x₂) : tau * b * tau⁻¹ = b⁻¹ := by
  refine Subgroup.closure_induction (p := fun b _ => tau * b * tau⁻¹ = b⁻¹) ?_ ?_ ?_ ?_ hb
  · intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact hc.tau_x₁
    · exact hc.tau_x₂
  · simp
  · intro y z hy hz ihy ihz
    have hyz : y * z = z * y :=
      comm_of_mem_W hc (Subgroup.mem_sup_right (show y ∈ baseGrp x₁ x₂ from hy))
        (Subgroup.mem_sup_right (show z ∈ baseGrp x₁ x₂ from hz))
    calc tau * (y * z) * tau⁻¹ = (tau * y * tau⁻¹) * (tau * z * tau⁻¹) := by group
      _ = y⁻¹ * z⁻¹ := by rw [ihy, ihz]
      _ = (y * z)⁻¹ := by rw [hyz]; group
  · intro y hy ihy
    rw [show tau * y⁻¹ * tau⁻¹ = (tau * y * tau⁻¹)⁻¹ by group, ihy]

private lemma fourGrp_le_baseGrp (hc : Ctx4 t L S x₁ x₂ lam rho tau) :
    fourGrp x₁ x₂ ≤ baseGrp x₁ x₂ := by
  rw [(hc.wreath.fourGrp_eq_omega).1]
  refine (Subgroup.closure_le (K := baseGrp x₁ x₂)).mpr ?_
  intro a ha
  exact ha.1

private lemma fourGrp_le_L_ctx4 (hc : Ctx4 t L S x₁ x₂ lam rho tau) :
    fourGrp x₁ x₂ ≤ L := by
  rw [fourGrp]
  refine (Subgroup.closure_le (K := L)).mpr ?_
  intro v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with rfl | rfl
  · exact (S4A.y_z_mem_L hc.toCtx0).1
  · exact (S4A.y_z_mem_L hc.toCtx0).2

private lemma baseGrp_le_W (hc : Ctx4 t L S x₁ x₂ lam rho tau) :
    baseGrp x₁ x₂ ≤ ctxW t x₁ x₂ := by
  show baseGrp x₁ x₂ ≤ twoCore t ⊔ baseGrp x₁ x₂
  exact le_sup_right

private lemma zpowers_t_le_W (hc : Ctx4 t L S x₁ x₂ lam rho tau) :
    Subgroup.zpowers t ≤ ctxW t x₁ x₂ := by
  rw [ctxW, ← hc.l43]
  exact le_sup_left

private lemma zpowers_inf_fourGrp (hc : Ctx4 t L S x₁ x₂ lam rho tau) :
    Subgroup.zpowers t ⊓ fourGrp x₁ x₂ = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨hxz, hxV⟩ := Subgroup.mem_inf.mp hx
  have ht2 : t * t = 1 := S4A.t_mul_self hc.hyp
  rcases mem_zpowers_eq_one_or_eq ht2 hxz with rfl | rfl
  · exact Subgroup.mem_bot.mpr rfl
  · exact absurd (fourGrp_le_L_ctx4 hc hxV) (S4A.t_not_mem_L hc.hyp)

private lemma card_zpowers_sup_V (hc : Ctx4 t L S x₁ x₂ lam rho tau) :
    Nat.card ↥(Subgroup.zpowers t ⊔ fourGrp x₁ x₂) = 8 := by
  have hnorm : ∀ k ∈ fourGrp x₁ x₂, ∀ h ∈ Subgroup.zpowers t,
      k * h * k⁻¹ ∈ Subgroup.zpowers t := by
    intro k hk h hh
    have hkh : k * h = h * k :=
      comm_of_mem_W hc (baseGrp_le_W hc (fourGrp_le_baseGrp hc hk)) (zpowers_t_le_W hc hh)
    rw [hkh, mul_assoc, mul_inv_cancel, mul_one]
    exact hh
  have h := card_sup_eq_mul hnorm (zpowers_inf_fourGrp hc)
  rw [Nat.card_zpowers, hc.hyp.ord_t, (hc.wreath.fourGrp_eq_omega).2.2] at h
  exact h

private lemma inf_W_centralizer_tau_le (hc : Ctx4 t L S x₁ x₂ lam rho tau) :
    ctxW t x₁ x₂ ⊓ centralizer ({tau} : Set G) ≤
      Subgroup.zpowers t ⊔ fourGrp x₁ x₂ := by
  intro c hc'
  obtain ⟨hcW, hcC⟩ := Subgroup.mem_inf.mp hc'
  have htau_c : c * tau = tau * c := Subgroup.mem_centralizer_singleton_iff.mp hcC
  have hW_eq : ctxW t x₁ x₂ = Subgroup.zpowers t ⊔ baseGrp x₁ x₂ := by rw [ctxW, hc.l43]
  rw [hW_eq] at hcW
  have hnorm : ∀ k ∈ baseGrp x₁ x₂, ∀ h ∈ Subgroup.zpowers t,
      k * h * k⁻¹ ∈ Subgroup.zpowers t := by
    intro k hk h hh
    have hkh : k * h = h * k :=
      comm_of_mem_W hc (baseGrp_le_W hc hk) (zpowers_t_le_W hc hh)
    rw [hkh, mul_assoc, mul_inv_cancel, mul_one]
    exact hh
  obtain ⟨p, hp, b, hb, hcp⟩ :=
    (mem_sup_iff_of_normalizes (H := Subgroup.zpowers t) (K := baseGrp x₁ x₂) hnorm).mp hcW
  have ht_tau : tau * t = t * tau := S4A.mem_invCent_iff.mp (hc.le_invCent hc.tau_mem)
  have hpC : p ∈ Subgroup.centralizer ({tau} : Set G) :=
    (Subgroup.zpowers_le.mpr
      (by rw [Subgroup.mem_centralizer_singleton_iff]; exact ht_tau.symm)) hp
  have htp_comm : p * tau = tau * p := Subgroup.mem_centralizer_singleton_iff.mp hpC
  have htp : tau * p * tau⁻¹ = p := by rw [← htp_comm]; group
  have htb : tau * b * tau⁻¹ = b⁻¹ := tau_conj_baseGrp hc hb
  have h1 : tau * c * tau⁻¹ = p * b⁻¹ := by
    rw [hcp]
    calc tau * (p * b) * tau⁻¹ = (tau * p * tau⁻¹) * (tau * b * tau⁻¹) := by group
      _ = p * b⁻¹ := by rw [htp, htb]
  have hc_eq : tau * c * tau⁻¹ = c := by rw [← htau_c]; group
  have hbinv : b⁻¹ = b := by
    have : p * b⁻¹ = p * b := by rw [← h1, hc_eq, hcp]
    exact mul_left_cancel this
  have hbb : b * b = 1 := by
    calc b * b = b * b⁻¹ := by rw [hbinv]
      _ = 1 := mul_inv_cancel b
  have hb2 : b ^ 2 = 1 := by rwa [pow_two]
  have hbV : b ∈ fourGrp x₁ x₂ := by
    rw [(hc.wreath.fourGrp_eq_omega).1]
    exact Subgroup.subset_closure ⟨hb, hb2⟩
  rw [hcp]
  exact Subgroup.mul_mem_sup hp hbV

private lemma ctxX_gen_pairwise_comm (hc : Ctx4 t L S x₁ x₂ lam rho tau) :
    ({t, tau, x₁ ^ 2, (x₁ * x₂) ^ 2} : Set G).Pairwise Commute := by
  have htt : Commute t tau := (S4A.mem_invCent_iff.mp (hc.le_invCent hc.tau_mem)).symm
  have hty : Commute t (x₁ ^ 2) :=
    (S4A.mem_invCent_iff.mp (S4A.L_le_invCent hc.hyp (S4A.y_z_mem_L hc.toCtx0).1)).symm
  have htz : Commute t ((x₁ * x₂) ^ 2) := S4A.t_commute_z hc.toCtx0
  have htay : Commute tau (x₁ ^ 2) := S4A.tau_commute_y hc.toCtx
  have htaz : Commute tau ((x₁ * x₂) ^ 2) := S4A.tau_commute_z hc.toCtx
  have hyz : Commute (x₁ ^ 2) ((x₁ * x₂) ^ 2) := S4A.y_commute_z hc.wreath
  intro a ha b hb hab
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
    first
      | exact absurd rfl hab
      | exact htt
      | exact htt.symm
      | exact hty
      | exact hty.symm
      | exact htz
      | exact htz.symm
      | exact htay
      | exact htay.symm
      | exact htaz
      | exact htaz.symm
      | exact hyz
      | exact hyz.symm

private lemma ctxX_comm (hc : Ctx4 t L S x₁ x₂ lam rho tau) :
    IsMulCommutative (ctxX t tau x₁ x₂) := by
  rw [ctxX]
  exact Subgroup.isMulCommutative_closure (ctxX_gen_pairwise_comm hc)

private lemma ctxX_sq_one (hc : Ctx4 t L S x₁ x₂ lam rho tau) :
    ∀ x ∈ ctxX t tau x₁ x₂, x ^ 2 = 1 := by
  haveI : IsMulCommutative (ctxX t tau x₁ x₂) := ctxX_comm hc
  intro x hx
  rw [ctxX] at hx
  induction hx using Subgroup.closure_induction with
  | mem z hz =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · simpa [pow_two] using S4A.t_mul_self hc.hyp
      · simpa [pow_two] using hc.l44.1
      · simpa [pow_two] using (S4A.y_mul_self_ne_one hc.wreath).1
      · simpa [pow_two] using (S4A.z_mul_self_ne_one hc.toCtx0).1
  | one => simp
  | mul x y hx hy ihx ihy =>
      have hcomm : Commute x y :=
        congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥(ctxX t tau x₁ x₂)) ⟨y, hy⟩)
      rw [hcomm.mul_pow, ihx, ihy, mul_one]
  | inv x hx ihx => rw [inv_pow, ihx, inv_one]

theorem l12_abelian_le_W (hc : Ctx4 t L S x₁ x₂ lam rho tau) {A : Subgroup G}
    (hA : A ≤ ctxW t x₁ x₂ ⊔ zpowers tau) (hab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hcard : Nat.card A = 32) : A = ctxW t x₁ x₂ := by
  by_cases hAW : A ≤ ctxW t x₁ x₂
  · exact Subgroup.eq_of_le_of_card_ge hAW (by rw [l12_card_W hc, hcard])
  · have hex : ∃ a, a ∈ A ∧ a ∉ ctxW t x₁ x₂ := by
      by_contra h
      apply hAW
      intro x hx
      by_contra hxW
      exact h ⟨x, hx, hxW⟩
    obtain ⟨a, haA, haW⟩ := hex
    have htau2 : tau * tau = 1 := by simpa [pow_two] using hc.l44.1
    have hnorm : ∀ k ∈ zpowers tau, ∀ h ∈ ctxW t x₁ x₂,
        k * h * k⁻¹ ∈ ctxW t x₁ x₂ := by
      intro k hk h hh
      rcases mem_zpowers_eq_one_or_eq htau2 hk with rfl | rfl
      · simpa using hh
      · exact l12_tau_normalizes_W hc h hh
    obtain ⟨w, hw, k, hk, hak⟩ :=
      (mem_sup_iff_of_normalizes (H := ctxW t x₁ x₂) (K := zpowers tau) hnorm).mp (hA haA)
    have hk_ne : k ≠ 1 := by
      intro hk1
      apply haW
      rw [hak, hk1, mul_one]
      exact hw
    rcases mem_zpowers_eq_one_or_eq htau2 hk with hk1 | hkτ
    · exact absurd hk1 hk_ne
    · have hle : A ⊓ ctxW t x₁ x₂ ≤ ctxW t x₁ x₂ ⊓ centralizer ({tau} : Set G) := by
        intro c hcc
        obtain ⟨hcA, hcW⟩ := Subgroup.mem_inf.mp hcc
        refine Subgroup.mem_inf.mpr ⟨hcW, ?_⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hca : c * a = a * c := hab c hcA a haA
        have hca' : c * (w * k) = (w * k) * c := by rw [← hak]; exact hca
        have h1 : c * (w * tau) = (w * tau) * c := by rw [hkτ] at hca'; exact hca'
        have hcw : c * w = w * c := comm_of_mem_W hc hcW hw
        have h2 : w * (c * tau) = w * (tau * c) := by
          calc w * (c * tau) = (w * c) * tau := by group
            _ = (c * w) * tau := by rw [← hcw]
            _ = c * (w * tau) := by group
            _ = (w * tau) * c := h1
            _ = w * (tau * c) := by group
        exact mul_left_cancel h2
      have hcard_inf : Nat.card ↥(A ⊓ ctxW t x₁ x₂) ≤ 8 := by
        calc Nat.card ↥(A ⊓ ctxW t x₁ x₂)
            ≤ Nat.card ↥(ctxW t x₁ x₂ ⊓ centralizer ({tau} : Set G)) :=
              Subgroup.card_le_of_le hle
          _ ≤ Nat.card ↥(Subgroup.zpowers t ⊔ fourGrp x₁ x₂) :=
              Subgroup.card_le_of_le (inf_W_centralizer_tau_le hc)
          _ = 8 := card_zpowers_sup_V hc
      have hrel : (ctxW t x₁ x₂).relIndex (ctxW t x₁ x₂ ⊔ zpowers tau) = 2 := by
        have h := Subgroup.relIndex_mul_card (H := ctxW t x₁ x₂)
          (K := ctxW t x₁ x₂ ⊔ zpowers tau)
        rw [inf_eq_left.mpr le_sup_left, l12_card_W hc, l12_card_W_tau hc] at h
        norm_num at h
        omega
      have hleA : Nat.card A ≤ 2 * Nat.card ↥(A ⊓ ctxW t x₁ x₂) :=
        card_le_two_mul_card_inf hA hrel
      exfalso
      omega

theorem l12_W_normal (hc : Ctx11 t L S x₁ x₂ lam rho tau) :
    NormalIn (ctxW t x₁ x₂) (ctxR t tau x₁ x₂) := by
  refine ⟨?_, ?_⟩
  · exact (le_sup_left : ctxW t x₁ x₂ ≤ ctxW t x₁ x₂ ⊔ zpowers tau).trans
      ((l12_W_tau_le_CRt hc).trans inf_le_left)
  · intro g hg k hk
    let A : Subgroup G := (ctxW t x₁ x₂).map (MulAut.conj g).toMonoidHom
    have hA_le : A ≤ ctxW t x₁ x₂ ⊔ zpowers tau := by
      intro x hx
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hx
      have hwCR : w ∈ ctxR t tau x₁ x₂ ⊓ centralizer ({t} : Set G) :=
        l12_W_tau_le_CRt hc (Subgroup.mem_sup_left hw)
      have hxCR : g * w * g⁻¹ ∈ ctxR t tau x₁ x₂ ⊓ centralizer ({t} : Set G) :=
        (l12_CRt_normal hc).2 g hg w hwCR
      rw [l12_CRt_eq hc] at hxCR
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hxCR
    have hAcard : Nat.card A = 32 := by
      dsimp only [A]
      rw [Subgroup.card_map_of_injective (K := ctxW t x₁ x₂)
          (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective,
        l12_card_W hc.toCtx10.toCtx4]
    have hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
      intro a ha b hb
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp ha
      obtain ⟨w', hw', rfl⟩ := Subgroup.mem_map.mp hb
      have hcomm : w * w' = w' * w := comm_of_mem_W hc.toCtx10.toCtx4 hw hw'
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc g * w * g⁻¹ * (g * w' * g⁻¹) = g * (w * w') * g⁻¹ := by group
        _ = g * (w' * w) * g⁻¹ := by rw [hcomm]
        _ = g * w' * g⁻¹ * (g * w * g⁻¹) := by group
    have hAeq : A = ctxW t x₁ x₂ :=
      l12_abelian_le_W hc.toCtx10.toCtx4 hA_le hAab hAcard
    have hmem : (MulAut.conj g) k ∈ A := Subgroup.mem_map.mpr ⟨k, hk, rfl⟩
    rw [hAeq] at hmem
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hmem

theorem l12_W_inf_Q (hc : Ctx11 t L S x₁ x₂ lam rho tau) :
    ctxW t x₁ x₂ ⊓ ctxQ t tau x₁ x₂ rho = baseGrp x₁ x₂ := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxW, hxQ⟩ := Subgroup.mem_inf.mp hx
    have hW_eq : ctxW t x₁ x₂ = Subgroup.zpowers t ⊔ baseGrp x₁ x₂ := by rw [ctxW, hc.l43]
    rw [hW_eq] at hxW
    have hnorm : ∀ k ∈ baseGrp x₁ x₂, ∀ h ∈ Subgroup.zpowers t,
        k * h * k⁻¹ ∈ Subgroup.zpowers t := by
      intro k hk h hh
      have hkh : k * h = h * k :=
        comm_of_mem_W hc.toCtx10.toCtx4 (baseGrp_le_W hc.toCtx10.toCtx4 hk)
          (zpowers_t_le_W hc.toCtx10.toCtx4 hh)
      rw [hkh, mul_assoc, mul_inv_cancel, mul_one]
      exact hh
    obtain ⟨p, hp, b, hb, hxp⟩ :=
      (mem_sup_iff_of_normalizes (H := Subgroup.zpowers t) (K := baseGrp x₁ x₂) hnorm).mp hxW
    have hpQ : p ∈ ctxQ t tau x₁ x₂ rho := by
      have : p = x * b⁻¹ := by rw [hxp]; group
      rw [this]
      exact (ctxQ t tau x₁ x₂ rho).mul_mem hxQ
        ((ctxQ t tau x₁ x₂ rho).inv_mem (hc.base_le_Q hb))
    have ht2 : t * t = 1 := S4A.t_mul_self hc.hyp
    rcases mem_zpowers_eq_one_or_eq ht2 hp with hp1 | hpt
    · rw [hxp, hp1, one_mul]; exact hb
    · exact absurd (hpt ▸ hpQ) (l12_t_not_mem_Q hc)
  · intro x hx
    exact Subgroup.mem_inf.mpr ⟨baseGrp_le_W hc.toCtx10.toCtx4 hx, hc.base_le_Q hx⟩

theorem l12_B_normal (hc : Ctx11 t L S x₁ x₂ lam rho tau) :
    NormalIn (baseGrp x₁ x₂) (ctxR t tau x₁ x₂) := by
  refine ⟨hc.base_le_Q.trans (l12_Q_le_R hc), ?_⟩
  intro g hg k hk
  have hgM : g ∈ ctxM t tau x₁ x₂ := (hc.normal_R).1 hg
  have hW : g * k * g⁻¹ ∈ ctxW t x₁ x₂ :=
    (l12_W_normal hc).2 g hg k (baseGrp_le_W hc.toCtx10.toCtx4 hk)
  have hQ : g * k * g⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
    hc.normal_Q.2 g hgM k (hc.base_le_Q hk)
  rw [← l12_W_inf_Q hc]
  exact Subgroup.mem_inf.mpr ⟨hW, hQ⟩

theorem l12_comm_B_mem_V (hc : Ctx11 t L S x₁ x₂ lam rho tau) {r b : G}
    (hr : r ∈ ctxR t tau x₁ x₂) (hb : b ∈ baseGrp x₁ x₂) :
    r * b * r⁻¹ * b⁻¹ ∈ fourGrp x₁ x₂ := by
  have hbR : b ∈ ctxR t tau x₁ x₂ := (hc.base_le_Q.trans (l12_Q_le_R hc)) hb
  have hB : r * b * r⁻¹ * b⁻¹ ∈ baseGrp x₁ x₂ :=
    (baseGrp x₁ x₂).mul_mem ((l12_B_normal hc).2 r hr b hb) ((baseGrp x₁ x₂).inv_mem hb)
  have hX : r * b * r⁻¹ * b⁻¹ ∈ ctxX t tau x₁ x₂ := hc.R_quot.2 r hr b hbR
  have hs2 : (r * b * r⁻¹ * b⁻¹) ^ 2 = 1 := ctxX_sq_one hc.toCtx10.toCtx4 _ hX
  rw [(hc.wreath.fourGrp_eq_omega).1]
  exact Subgroup.subset_closure ⟨hB, hs2⟩

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
