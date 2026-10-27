module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Core73c
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Core73b

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec7.C73

open Subgroup CFSG.GH74.GLS.Stage1.Thm3.Sec7

variable {G : Type*} [Group G]

theorem core73 {z t : G} {S P₁ P₂ Q₁ Q₂ S₁ : Subgroup G} [Finite G]
    (c : Ctx73 z t S P₁ P₂ Q₁ Q₂ S₁) :
    (P₁ ⊔ P₂).relIndex S₁ ≤ 2 ∧ Q₁ = P₂ ∧ Q₂ = P₁ := by
  by_contra hn
  obtain ⟨h4, hQ₁, hQ₂, idx₁, idx₂⟩ := c.not_concl73 hn
  have h8 := c.relIdx8 h4
  obtain ⟨v₂, hv₂Q, hv₂P, hv₂sq⟩ := c.exists_v₂ hQ₁
  obtain ⟨Y, hYS, hY2, hPY, hv₂Y, hnm⟩ := c.exists_Y_data h4 hv₂Q hv₂P
  obtain ⟨a', b', M, hQG, ha'Q, hb'Q, hgen', hzM, ⟨m, hm⟩, hM4, hcQ₂⟩ :=
    data_of_quat (c.S2.to_le (c.Q₂S₁.trans c.S₁S)) c.P₁Q₂ idx₂ c.P₁card (c.P₁Q₂ c.zP₁) c.z_sq
      c.z_ne c.Q₂q
  obtain ⟨a₁, b₁, M₁, hQG₁, ha₁Q, hb₁Q, hgen₁, hzM₁, h4M₁, hM₁4, hcQ₁⟩ :=
    data_of_quat (c.S2.to_le (c.Q₁S₁.trans c.S₁S)) c.P₂Q₁ idx₁ c.P₂card (c.P₂Q₁ c.zP₂) c.z_sq
      c.z_ne c.Q₁q
  have hv₁P : a' ^ (2 * m) ∈ P₁ := by
    have := A.sq_mem_of_relIndex_two idx₂ (Q₂.pow_mem ha'Q m)
    rwa [← pow_add, ← two_mul] at this
  have hv₁sq : a' ^ (2 * m) * a' ^ (2 * m) = z := by
    rw [← pow_add, hzM, hm]; congr 1; ring
  have hv₁Z : a' ^ (2 * m) ∈ zpowers a' := Subgroup.pow_mem _ (mem_zpowers a') _
  obtain ⟨g, hg, hzg⟩ := c.exists_g Y hYS hY2 hPY hv₂Q hv₂P hv₂sq hv₂Y hnm hv₁P hv₁sq
  have hnc : ¬ IsCyclic ↥P₁ := not_isCyclic_of_quat c.P₁q c.P₁card
  obtain ⟨w₁, hw₁P, hw₁n⟩ : ∃ w₁ ∈ P₁, w₁ ∉ zpowers a' := by
    by_contra hcon
    push Not at hcon
    exact hnc (Subgroup.isCyclic_of_le (fun x hx => hcon x hx) : IsCyclic ↥P₁)
  have hw₁Q : w₁ ∈ Q₂ := c.P₁Q₂ hw₁P
  obtain ⟨k, hk⟩ : ∃ k : ℕ, w₁ = a' ^ k * b' := by
    obtain ⟨k, hk | hk⟩ := hgen' w₁ hw₁Q
    · exfalso
      apply hw₁n
      rw [hk]; exact Subgroup.pow_mem _ (mem_zpowers a') k
    · exact ⟨k, hk⟩
  have hw₁sq : w₁ * w₁ = z := by rw [hk, hQG.akb_sq, hzM]
  have hw₁inv : ∀ x ∈ zpowers a', w₁ * x * w₁⁻¹ = x⁻¹ := fun x hx => by
    rw [hk]; exact hQG.akb_inv k hx
  obtain ⟨w₂, hw₂P, hw₂sq, hw₂inv⟩ := hQG₁.exists_w2 (Q := Q₁) (Mm := P₂) hzM₁ ha₁Q hgen₁ h4M₁
    (fun x hx => A.sq_mem_of_relIndex_two idx₁ hx) hv₂Q hv₂P hv₂sq
  have hzw₁ : z * w₁ = w₁ * z := (c.P₁P₂ w₁ hw₁P z c.zP₂).symm
  have hzw₂ : z * w₂ = w₂ * z := c.P₁P₂ z c.zP₁ w₂ hw₂P
  have hzv₂ : z * v₂ = v₂ * z := (c.Q₁P₁ v₂ hv₂Q z c.zP₁).symm
  have h3 : w₂ * a' ^ (2 * m) = a' ^ (2 * m) * w₂ := (c.P₁P₂ _ hv₁P w₂ hw₂P).symm
  have h4' : w₁ * v₂ = v₂ * w₁ := (c.Q₁P₁ v₂ hv₂Q w₁ hw₁P).symm
  have hw12 : w₁ * w₂ = w₂ * w₁ := c.P₁P₂ w₁ hw₁P w₂ hw₂P
  have h1 : w₁ * a' ^ (2 * m) = a' ^ (2 * m) * w₁ * z :=
    comm_aux c.z_sq hv₁sq hzw₁ (hw₁inv _ hv₁Z)
  have h2 : w₂ * v₂ = v₂ * w₂ * z := comm_aux c.z_sq hv₂sq hzw₂ hw₂inv
  have hww : (w₁ * w₂) * (w₁ * w₂) = 1 := by
    calc w₁ * w₂ * (w₁ * w₂) = w₁ * (w₂ * w₁) * w₂ := by group
      _ = w₁ * (w₁ * w₂) * w₂ := by rw [← hw12]
      _ = (w₁ * w₁) * (w₂ * w₂) := by group
      _ = 1 := by rw [hw₁sq, hw₂sq]; exact c.z_sq
  have hvw : (w₁ * w₂) * (a' ^ (2 * m) * v₂) = (a' ^ (2 * m) * v₂) * (w₁ * w₂) := by
    calc w₁ * w₂ * (a' ^ (2 * m) * v₂) = w₁ * (w₂ * a' ^ (2 * m)) * v₂ := by group
      _ = w₁ * (a' ^ (2 * m) * w₂) * v₂ := by rw [h3]
      _ = (w₁ * a' ^ (2 * m)) * (w₂ * v₂) := by group
      _ = (a' ^ (2 * m) * w₁ * z) * (v₂ * w₂ * z) := by rw [h1, h2]
      _ = a' ^ (2 * m) * w₁ * (z * v₂) * w₂ * z := by group
      _ = a' ^ (2 * m) * w₁ * (v₂ * z) * w₂ * z := by rw [hzv₂]
      _ = a' ^ (2 * m) * (w₁ * v₂) * (z * w₂) * z := by group
      _ = a' ^ (2 * m) * (v₂ * w₁) * (w₂ * z) * z := by rw [h4', hzw₂]
      _ = a' ^ (2 * m) * v₂ * w₁ * w₂ * (z * z) := by group
      _ = (a' ^ (2 * m) * v₂) * (w₁ * w₂) := by rw [c.z_sq, mul_one]; group
  have hwS : w₁ * w₂ ∈ S := S.mul_mem (c.P₁S hw₁P) (c.P₂S hw₂P)
  have hw₂nz : w₂ ∉ zpowers z := sq_not_mem_zpowers c.z_sq c.z_ne hw₂sq
  have ha'S : a' ∈ S := c.S₁S (c.Q₂S₁ ha'Q)
  have ha'2P : a' ^ 2 ∈ P₁ := by
    rw [pow_two]; exact A.sq_mem_of_relIndex_two idx₂ ha'Q
  have hT₁P : zpowers (a' ^ 2) ≤ P₁ := zpowers_le.2 ha'2P
  have hT₁le : zpowers (a' ^ 2) ≤ zpowers a' :=
    zpowers_le.2 (Subgroup.pow_mem _ (mem_zpowers a') 2)
  have hzT₁ : z ∈ zpowers (a' ^ 2) := by
    have : z = (a' ^ 2) ^ (2 * m) := by rw [hzM, hm, ← pow_mul]; congr 1; ring
    rw [this]; exact Subgroup.pow_mem _ (mem_zpowers _) _
  have hcardT₁ : Nat.card ↥(zpowers (a' ^ 2)) = M := by
    rw [Nat.card_zpowers,
      orderOf_pow_of_dvd (by norm_num) (by rw [hQG.ord]; exact dvd_mul_right 2 M), hQG.ord]
    omega
  have hwinv₁ : ∀ x ∈ zpowers (a' ^ 2), (w₁ * w₂) * x * (w₁ * w₂)⁻¹ = x⁻¹ := by
    intro x hx
    have hw2x : w₂ * x * w₂⁻¹ = x := by
      rw [← c.P₁P₂ x (hT₁P hx) w₂ hw₂P]; group
    calc w₁ * w₂ * x * (w₁ * w₂)⁻¹ = w₁ * (w₂ * x * w₂⁻¹) * w₁⁻¹ := by group
      _ = w₁ * x * w₁⁻¹ := by rw [hw2x]
      _ = x⁻¹ := hw₁inv x (hT₁le hx)
  have hwT₁ : w₁ * w₂ ∉ zpowers (a' ^ 2) := by
    intro h
    have h1 : w₁ * w₂ ∈ P₁ := hT₁P h
    have : w₂ ∈ P₁ := by
      have := P₁.mul_mem (P₁.inv_mem hw₁P) h1
      simpa using this
    exact hw₂nz (c.P₁₂ ⟨this, hw₂P⟩)
  have hvT₁ : ∀ x ∈ zpowers (a' ^ 2), x * (a' ^ (2 * m) * v₂) = (a' ^ (2 * m) * v₂) * x := by
    intro x hx
    have hc1 : x * a' ^ (2 * m) = a' ^ (2 * m) * x := by
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 (hT₁le hx)
      exact (((Commute.refl a').zpow_left j).pow_right (2 * m)).eq
    have hc2 : v₂ * x = x * v₂ := c.Q₁P₁ v₂ hv₂Q x (hT₁P hx)
    calc x * (a' ^ (2 * m) * v₂) = (x * a' ^ (2 * m)) * v₂ := by group
      _ = a' ^ (2 * m) * (x * v₂) := by rw [hc1]; group
      _ = a' ^ (2 * m) * (v₂ * x) := by rw [hc2]
      _ = (a' ^ (2 * m) * v₂) * x := by group
  obtain ⟨hb1, hc1', hd1, he1⟩ := c.pass (T := zpowers (a' ^ 2)) (w := w₁ * w₂) (g := g)
    (v := a' ^ (2 * m) * v₂) inferInstance (hT₁P.trans c.P₁S) hzT₁ (by omega) hwS hww hwinv₁
    hwT₁ hvT₁ hvw hg hzg
  rw [h8, hcardT₁] at hb1
  have hM : M = 4 := by omega
  have hP₁8 : Nat.card ↥P₁ = 8 := by
    have := A.card_eq_two_mul_of_relIndex_two c.P₁Q₂ idx₂
    omega
  have hP₂8 : Nat.card ↥P₂ = 8 := by rw [← c.card_P₁_eq_P₂]; exact hP₁8
  have hM₁ : M₁ = 4 := by
    have := A.card_eq_two_mul_of_relIndex_two c.P₂Q₁ idx₁
    omega
  set D : Subgroup G := zpowers (a' ^ 2) ⊔ zpowers (w₁ * w₂) with hD
  set Dg : Subgroup G := D.map (MulAut.conj g⁻¹).toMonoidHom with hDg
  have hmemDg : ∀ x, x ∈ Dg ↔ ∃ d ∈ D, g⁻¹ * d * g = x := by
    intro x
    simp only [hDg, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hDgS : Dg ≤ S := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := (hmemDg x).1 hx
    exact he1 d hd
  have hDgP : Dg ⊓ (P₁ ⊔ P₂) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx, hxP⟩
    obtain ⟨d, hd, rfl⟩ := (hmemDg x).1 hx
    rw [hd1 d hd hxP]
    simp
  have hcardDg : Nat.card ↥Dg = 8 := by
    rw [hDg, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hc1', hcardT₁]
    omega
  set U : Subgroup G := Dg ⊓ S₁ with hU
  have hUsq : ∀ x ∈ U, x * x = 1 := by
    intro x hx
    have h1 : x * x ∈ P₁ ⊔ P₂ := c.d₂ h4 x hx.2
    have h2 : x * x ∈ Dg := Dg.mul_mem hx.1 hx.1
    have : x * x ∈ Dg ⊓ (P₁ ⊔ P₂) := ⟨h2, h1⟩
    rw [hDgP] at this
    exact this
  have hUle : Nat.card ↥U ≤ 4 := by
    have := B.card_le_relIndex_of_trivial_inf (S := S₁) (P := P₁ ⊔ P₂) (D := U) (g := 1)
      (fun s hs p hp => c.PnS s (c.S₁S hs) p hp) (fun x hx => by simpa using hx.2)
      (fun x hx hxP => by
        have : x ∈ Dg ⊓ (P₁ ⊔ P₂) := ⟨hx.1, by simpa using hxP⟩
        rw [hDgP] at this; exact this)
    rwa [h4] at this
  have hUge : 4 ≤ Nat.card ↥U := by
    have hr : S₁.relIndex Dg ≤ S₁.relIndex S := by
      have hne : S₁.relIndex S ≠ 0 := by rw [c.S₁idx]; norm_num
      exact Subgroup.relIndex_le_of_le_right hDgS hne
    rw [c.S₁idx] at hr
    have h1 := Subgroup.relIndex_mul_card S₁ Dg
    rw [inf_comm, ← hU, hcardDg] at h1
    generalize S₁.relIndex Dg = r at hr h1
    interval_cases r <;> omega
  have hUeq : Nat.card ↥U = 4 := by omega
  have hPU : (P₁ ⊔ P₂) ⊓ U = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxP, hxU⟩
    have : x ∈ Dg ⊓ (P₁ ⊔ P₂) := ⟨hxU.1, hxP⟩
    rw [hDgP] at this
    exact this
  have hS₁eq : S₁ = P₁ ⊔ P₂ ⊔ U := by
    have hUn : U ≤ normalizer ((P₁ ⊔ P₂ : Subgroup G) : Set G) := by
      intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro p
      have hxS : x ∈ S := c.S₁S hx.2
      constructor
      · intro hp; exact c.PnS x hxS p hp
      · intro hp
        have := c.PnS x⁻¹ (S.inv_mem hxS) _ hp
        simpa [mul_assoc] using this
    have h1 := A.card_sup_mul_card_inf hUn
    rw [hPU, Subgroup.card_bot, hUeq] at h1
    have h2 := Subgroup.relIndex_mul_card (P₁ ⊔ P₂) S₁
    rw [inf_eq_left.2 c.P_le_S₁, h4] at h2
    have hle : P₁ ⊔ P₂ ⊔ U ≤ S₁ := sup_le c.P_le_S₁ inf_le_right
    exact (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm
  have hS₁Q : S₁ = Q₂ ⊔ Q₁ := by rw [sup_comm]; exact c.d₁ h4
  have hQ₁4 : Nonempty (↥Q₁ ≃* QuaternionGroup 4) := by
    obtain ⟨N, hNZ, ⟨e⟩⟩ := c.Q₁q
    have hN : N = 4 := by have := A.card_quat e; omega
    subst hN; exact ⟨e⟩
  have hQ₂4 : Nonempty (↥Q₂ ≃* QuaternionGroup 4) := by
    obtain ⟨N, hNZ, ⟨e⟩⟩ := c.Q₂q
    have hN : N = 4 := by have := A.card_quat e; omega
    subst hN; exact ⟨e⟩
  have hP₁2 : Nonempty (↥P₁ ≃* QuaternionGroup 2) := by
    obtain ⟨N, hNZ, ⟨e⟩⟩ := c.P₁q
    have hN : N = 2 := A.N_eq_two_of_card e hP₁8
    subst hN; exact ⟨e⟩
  have hP₂2 : Nonempty (↥P₂ ≃* QuaternionGroup 2) := by
    obtain ⟨N, hNZ, ⟨e⟩⟩ := c.P₂q
    have hN : N = 2 := A.N_eq_two_of_card e hP₂8
    subst hN; exact ⟨e⟩
  have hcen₁ := center_map_eq hQG₁ (by omega) ha₁Q hb₁Q hgen₁ hzM₁
  have hcen₂ := center_map_eq hQG (by omega) ha'Q hb'Q hgen' hzM
  have hQ₁C : Q₁ = S₁ ⊓ centralizer (P₁ : Set G) := by
    apply le_antisymm
    · intro x hx
      exact ⟨c.Q₁S₁ hx, Subgroup.mem_centralizer_iff.2 (fun h hh => (c.Q₁P₁ x hx h hh).symm)⟩
    · rintro x ⟨hxS, hxc⟩
      exact c.C₁ x hxS (fun p hp => (Subgroup.mem_centralizer_iff.1 hxc p hp).symm)
  have hQ₂C : Q₂ = S₁ ⊓ centralizer (P₂ : Set G) := by
    apply le_antisymm
    · intro x hx
      exact ⟨c.Q₂S₁ hx, Subgroup.mem_centralizer_iff.2 (fun h hh => (c.Q₂P₂ x hx h hh).symm)⟩
    · rintro x ⟨hxS, hxc⟩
      exact c.C₂ x hxS (fun p hp => (Subgroup.mem_centralizer_iff.1 hxc p hp).symm)
  have hcomm : ∀ a ∈ Q₁, ∀ b ∈ Q₂, a * b = b * a :=
    c.h225 S₁ P₁ P₂ Q₁ Q₂ U c.S₁_pgroup hS₁eq hS₁Q c.S₁Q₁ c.S₁Q₂ hQ₁4 hQ₂4 c.Q₁Q₂ hcen₁ hcen₂
      hP₁2 hP₂2 c.P₂Q₁ c.P₁Q₂ hQ₁C hQ₂C hUsq hUeq hPU
  have hT₂S : zpowers a' ≤ S := zpowers_le.2 ha'S
  have hT₂Q : zpowers a' ≤ Q₂ := zpowers_le.2 ha'Q
  have hzT₂ : z ∈ zpowers a' := by rw [hzM]; exact Subgroup.pow_mem _ (mem_zpowers a') M
  have hcardT₂ : Nat.card ↥(zpowers a') = 8 := by
    rw [Nat.card_zpowers, hQG.ord]; omega
  have hwinv₂ : ∀ x ∈ zpowers a', (w₁ * w₂) * x * (w₁ * w₂)⁻¹ = x⁻¹ := by
    intro x hx
    have hw2x : w₂ * x * w₂⁻¹ = x := by
      rw [hcomm w₂ (c.P₂Q₁ hw₂P) x (hT₂Q hx)]; group
    calc w₁ * w₂ * x * (w₁ * w₂)⁻¹ = w₁ * (w₂ * x * w₂⁻¹) * w₁⁻¹ := by group
      _ = w₁ * x * w₁⁻¹ := by rw [hw2x]
      _ = x⁻¹ := hw₁inv x hx
  have hwT₂ : w₁ * w₂ ∉ zpowers a' := by
    intro h
    have h1 : w₁ * w₂ ∈ Q₂ := hT₂Q h
    have : w₂ ∈ Q₂ := by
      have := Q₂.mul_mem (Q₂.inv_mem (c.P₁Q₂ hw₁P)) h1
      simpa using this
    have h2 : w₂ ∈ Q₁ ⊓ Q₂ := ⟨c.P₂Q₁ hw₂P, this⟩
    rw [c.Q₁Q₂] at h2
    exact hw₂nz h2
  have hvT₂ : ∀ x ∈ zpowers a', x * (a' ^ (2 * m) * v₂) = (a' ^ (2 * m) * v₂) * x := by
    intro x hx
    have hc1 : x * a' ^ (2 * m) = a' ^ (2 * m) * x := by
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hx
      exact (((Commute.refl a').zpow_left j).pow_right (2 * m)).eq
    have hc2 : v₂ * x = x * v₂ := hcomm v₂ hv₂Q x (hT₂Q hx)
    calc x * (a' ^ (2 * m) * v₂) = (x * a' ^ (2 * m)) * v₂ := by group
      _ = a' ^ (2 * m) * (x * v₂) := by rw [hc1]; group
      _ = a' ^ (2 * m) * (v₂ * x) := by rw [hc2]
      _ = (a' ^ (2 * m) * v₂) * x := by group
  obtain ⟨hb2, -, -, -⟩ := c.pass (T := zpowers a') (w := w₁ * w₂) (g := g)
    (v := a' ^ (2 * m) * v₂) inferInstance hT₂S hzT₂ (by omega) hwS hww hwinv₂ hwT₂ hvT₂ hvw hg hzg
  rw [h8, hcardT₂] at hb2
  omega

end CFSG.GH74.GLS.Stage1.Thm3.Sec7.C73
