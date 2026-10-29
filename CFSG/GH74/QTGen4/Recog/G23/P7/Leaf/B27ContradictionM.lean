module

public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.B27ContradictionL
public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.B27ContradictionF
public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.B27ContradictionG
public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.B27ContradictionJ
public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.B27ContradictionK

public section

namespace CFSG.GH74.QTGen4.Recog.G23.P7

open CFSG.Open CFSG.Quasithin.G23Type CFSG.GH74.QTGen4.Recog.G23 CFSG.CosetTable
open CFSG.GH74.QTGen4.Recog.G23.P7.B27A
open scoped commutatorElement IsMulCommutative

variable {G : Type} [Group G]

theorem cube_one_of_conj [Finite G] {H H₁ H₂ : Subgroup G} {e : Fin 6 → G}
    (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e) (hF : HFacts H H₁ H₂ e)
    (c0 u x : G) (hc0 : c0 * zOf e * c0⁻¹ = u) (hux : u * x = x * u) (k : ℕ)
    (hk : x ^ (3 ^ k) = 1) : x ^ 3 = 1 := by
  have hy : c0⁻¹ * x * c0 ∈ H := by
    rw [mem_H_iff_zOf hone hlet]
    rw [← hc0] at hux
    calc zOf e * (c0⁻¹ * x * c0) = c0⁻¹ * (c0 * zOf e * c0⁻¹ * x) * c0 := by group
      _ = c0⁻¹ * (x * (c0 * zOf e * c0⁻¹)) * c0 := by rw [hux]
      _ = (c0⁻¹ * x * c0) * zOf e := by group
  have hconj : ∀ n : ℕ, (c0⁻¹ * x * c0) ^ n = c0⁻¹ * x ^ n * c0 := fun n => by
    rw [show c0⁻¹ * x * c0 = c0⁻¹ * x * (c0⁻¹)⁻¹ by rw [inv_inv], conj_pow, inv_inv]
  have h3 := cube_one_of_H hF _ hy k (by rw [hconj, hk, mul_one, inv_mul_cancel])
  rw [hconj] at h3
  calc x ^ 3 = c0 * (c0⁻¹ * x ^ 3 * c0) * c0⁻¹ := by group
    _ = 1 := by rw [h3, mul_one, mul_inv_cancel]

theorem main_contradiction [Finite G] [G23Leaf LeafGL3Facts]
    {T H H₁ H₂ M : Subgroup G} {e : Fin 6 → G} {M₁ M₂ Pb Np Nm W₁ Mf : Subgroup G} {t' : G}
    (h : Setup G T H H₁ H₂ M e) (hF : HFacts H H₁ H₂ e) (hO : OneClass e)
    (hL : Local3 e H H₁ H₂ M₁ M₂ Pb Np Nm) (hPb : Nat.card Pb = 27)
    (ha₁ : IsElemAbelian 3 M₁) (ha₂ : IsElemAbelian 3 M₂) (hst : B27State e M₁ Pb W₁ Mf t') :
    False := by
  have hone : G23One H H₁ H₂ := h.ctx.one
  have hlet : HLetters H H₁ H₂ e := h.lets
  have hv : VertexCore e H (e 0) H₂ M₁ := hL.v₁
  have hM1 : Nat.card M₁ = 27 := card_M₁ hL hPb
  have hC : Nat.card (Subgroup.centralizer ({e 0} : Set G)) = 648 := card_cent_e0 hone hL hPb
  haveI hMc : IsMulCommutative M₁ := ha₁.1
  haveI hmod : Module (ZMod 3) (Additive M₁) := AddCommGroup.zmodModule (exp3_add ha₁)
  have hexp : ∀ m ∈ M₁, m ^ 3 = 1 := ha₁.2
  obtain ⟨w, hwM, d, hdM, b, hwW, hw1, hdD, hb0, hb1, hb2⟩ :=
    gl3_basis hone hlet hv hst hM1 hexp
  have hwD : w ∈ Dg (zOf e) M₁ (zOf_conj_M₁ hone hlet hv) :=
    (mem_Dg (zOf e) M₁ (zOf_conj_M₁ hone hlet hv) w).mpr ⟨hwM, hst.W₁_inv w hwW⟩
  have hw3 : w ^ 3 = 1 := hexp w hwM
  have hWeq : W₁ = Subgroup.zpowers w := by
    have hord : orderOf w = 3 := orderOf_eq_prime hw3 hw1
    exact (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hwW)
      (by rw [Nat.card_zpowers, hord, hst.card_W₁])).symm
  have hY0 : Y0Subgroup ≤ (rhoGL b).range :=
    Y0Subgroup_le_range hone hlet hF hv hst b w d hwM hdM hb0 hb1 hb2 hwD hdD
  have h13 : ¬ 13 ∣ Nat.card (rhoGL b).range :=
    not_dvd13 hone hlet hv hst hC b hb0 w hwM hwW hw1 hWeq hw3 hb1
  have hmove := exists_move_line hone hlet hv hst b hb0 hM1
  have hLGL := (G23Leaf.out (L := LeafGL3Facts)).2 (rhoGL b).range (fun g hg => hY0 hg) h13 hmove
  have hstabB := hLGL.1
  have h27 : 27 ∣ Nat.card (rhoGL b).range := dvd_trans (by norm_num) hLGL.2
  have hU0 : U0 ≤ (rhoGL b).range := U0_le_of_stab _ hstabB h27
  have hMbar := card_Mbar hone hlet hv hst b hM1 hU0
  have hMfN : Mf ≤ Subgroup.normalizer (Mbar b : Set G) := Mf_le_normalizer_Mbar hst b hstabB
  have hnot : ¬ Mf ≤ Mbar b := Mf_not_le_Mbar hone hlet hF hv hst b hb0
  obtain ⟨hS729', hSdvd⟩ := card_S_bounds Mf (Mbar b) hnot hMfN hst.card_Mf hMbar
  have hSodd : Odd (Nat.card ↥(Mf ⊔ Mbar b)) := Odd.of_dvd_nat (by decide) hSdvd
  have hE4 : Nat.card ↥(Esub e) = 4 := Esub_card hone hlet
  have hEsq := Esub_sq hone hlet
  have hEN1 : Esub e ≤ Subgroup.normalizer (M₁ : Set G) := by
    unfold Esub
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact e4_mem_normalizer_M₁ hlet hv
    · exact zOf_mem_normalizer_M₁ hone hlet hv
  have hEP : Esub e ≤ Subgroup.normalizer (Pb : Set G) := hst.compl.right_le
  have hEnorm : ∀ a ∈ Esub e, ∀ x ∈ Mf ⊔ Mbar b, a * x * a⁻¹ ∈ Mf ⊔ Mbar b := by
    intro a ha
    have hmapS : Mf ⊔ Mbar b ≤ (Mf ⊔ Mbar b).comap (MulAut.conj a).toMonoidHom := by
      refine sup_le ?_ ?_
      · intro x hx
        exact Subgroup.mem_sup_left (hst.compl.conj_mem a (hEP ha) x hx)
      · intro x hx
        exact Subgroup.mem_sup_right (Mbar_conj_mem b hstabB a (hEN1 ha) x hx)
    intro x hx
    exact hmapS hx
  have hWMf : W₁ ≤ Mf := hst.W₁_le.trans (inf_le_left.trans hst.M₁_le)
  have ht'E : t' ∈ Esub e := by
    rcases hst.t'_mem with h1 | h1
    · rw [h1]
      exact Subgroup.subset_closure (by simp)
    · rw [h1]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  have ht'ord : orderOf t' = 2 := by
    rcases hst.t'_mem with h1 | h1
    · rw [h1]
      exact orderOf_e4 hone hlet
    · rw [h1]
      exact orderOf_e4z hone hlet
  have ht'1 : t' ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at ht'ord
    norm_num at ht'ord
  obtain ⟨hSeq, hBcard⟩ := four_group_bw (Esub e) (Mf ⊔ Mbar b) hE4 hEsq hEnorm hSodd hS729'
    (fun a ha ha1 => card_centralizer_inf_dvd_nine hone hlet hF hO (Mf ⊔ Mbar b) hSdvd a
      (hEsq a ha) ha1) t' ht'E ht'1
  obtain ⟨B, hBdef⟩ : ∃ B : Subgroup G,
      B = Subgroup.centralizer ({t'} : Set G) ⊓ (Mf ⊔ Mbar b) := ⟨_, rfl⟩
  have hBcard' : Nat.card ↥B = 9 := by
    rw [hBdef]
    exact hBcard
  have hBmem : ∀ y ∈ B, y ∈ Subgroup.centralizer ({t'} : Set G) ∧ y ∈ Mf ⊔ Mbar b := by
    intro y hy
    rw [hBdef] at hy
    exact Subgroup.mem_inf.mp hy
  have hBt : ∀ y ∈ B, t' * y = y * t' := fun y hy =>
    Subgroup.mem_centralizer_iff.mp (hBmem y hy).1 t' (Set.mem_singleton t')
  have hBS : ∀ y ∈ B, y ∈ Mf ⊔ Mbar b := fun y hy => (hBmem y hy).2
  obtain ⟨c, hc⟩ := conj_zOf_of_orderOf hO t' ht'ord
  obtain ⟨g, hg⟩ := exists_conj_Psub_le hone hlet hF c hc B hBt hBcard'
  have hWB : W₁ ≤ B := by
    intro w hw
    rw [hBdef]
    refine Subgroup.mem_inf.mpr ⟨?_, Subgroup.mem_sup_left (hWMf hw)⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact mul_inv_eq_iff_eq_mul.mp (hst.W₁_cent w hw)
  have hBnotW : ¬ B ≤ W₁ := fun hle => by
    have h := Subgroup.card_le_of_le hle
    rw [hBcard', hst.card_W₁] at h
    omega
  obtain ⟨σ, hσB, hσW⟩ : ∃ σ ∈ B, σ ∉ W₁ := by
    by_contra hcon
    push Not at hcon
    exact hBnotW hcon
  have hPeq : (Psub e).map (MulAut.conj g).toMonoidHom = B := by
    apply Subgroup.eq_of_le_of_card_ge
    · intro y hy
      obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hy
      exact hg p hp
    · rw [Subgroup.card_map_of_injective (MulEquiv.injective _), hF.card_P, hBcard']
  have hσ3 : σ ^ 3 = 1 := by
    have hσmap : σ ∈ (Psub e).map (MulAut.conj g).toMonoidHom := by
      rw [hPeq]
      exact hσB
    obtain ⟨p, hp, hpσ⟩ := Subgroup.mem_map.mp hσmap
    rw [← hpσ]
    show (g * p * g⁻¹) ^ 3 = 1
    rw [conj_pow, hF.elem_P.2 p hp, mul_one, mul_inv_cancel]
  have hσ1 : σ ≠ 1 := fun h1 => hσW (h1 ▸ W₁.one_mem)
  have hσMf : σ ∉ Mf := by
    intro hm
    have hc' : σ ∈ Mf ⊓ Subgroup.centralizer ({t'} : Set G) :=
      Subgroup.mem_inf.mpr ⟨hm, (hBmem σ hσB).1⟩
    rw [hst.cent_t'] at hc'
    exact hσW hc'
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI hBmc : IsMulCommutative ↥B :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hBcard']; norm_num)
  have hBcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥B) ⟨y, hy⟩)
  have hBeq : Subgroup.zpowers σ ⊔ W₁ = B :=
    B_eq_sup B W₁ hBcard' hst.card_W₁ hWB σ hσB hσ3 hσW hBcomm
  have hσWc : ∀ w ∈ W₁, σ * w * σ⁻¹ = w := fun w hw => by
    rw [hBcomm σ hσB w (hWB hw), mul_inv_cancel_right]
  have hMfS : ∀ s ∈ Mf ⊔ Mbar b, ∀ x ∈ Mf, s * x * s⁻¹ ∈ Mf := by
    have hMfle : Mf ≤ Mf ⊔ Mbar b := le_sup_left
    have hidx : (Mf.subgroupOf (Mf ⊔ Mbar b)).index = 3 := by
      have hc'' := Subgroup.card_mul_index (Mf.subgroupOf (Mf ⊔ Mbar b))
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMfle).toEquiv, hst.card_Mf, hSeq] at hc''
      omega
    have hNorm : (Mf.subgroupOf (Mf ⊔ Mbar b)).Normal :=
      Subgroup.normal_of_index_eq_minFac_card (by rw [hidx, hSeq]; norm_num)
    intro s hs x hx
    have h := hNorm.conj_mem ⟨x, hMfle hx⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨s, hs⟩
    exact Subgroup.mem_subgroupOf.mp h
  have hσN : ∀ x ∈ Mf, σ * x * σ⁻¹ ∈ Mf := fun x hx => hMfS σ (hBS σ hσB) x hx
  have hcomm' : ∀ x ∈ Mf, ∀ y ∈ Mf, x⁻¹ * y⁻¹ * x * y ∈ W₁ := by
    intro x hx y hy
    have hmem : ⁅x⁻¹, y⁻¹⁆ ∈ W₁ := by
      rw [← hst.derived]
      exact Subgroup.commutator_mem_commutator (Mf.inv_mem hx) (Mf.inv_mem hy)
    rw [commutatorElement_def, inv_inv, inv_inv] at hmem
    exact hmem
  have hWexp : ∀ w ∈ W₁, w ^ 3 = 1 := fun w hw => by
    have h := (pow_card_eq_one' : (⟨w, hw⟩ : ↥W₁) ^ Nat.card ↥W₁ = 1)
    rw [hst.card_W₁] at h
    exact congrArg Subtype.val h
  have ht2 : t' ^ 2 = 1 := by
    have h := pow_orderOf_eq_one t'
    rw [ht'ord] at h
    exact h
  have hzE : zOf e ∈ Esub e := Subgroup.subset_closure (by simp)
  have hz2 : zOf e ^ 2 = 1 := by
    rw [pow_two]
    exact zOf_mul_self hone hlet
  have htN : ∀ x ∈ Mf, t' * x * t'⁻¹ ∈ Mf := fun x hx =>
    hst.compl.conj_mem t' (hEP ht'E) x hx
  have hzN : ∀ x ∈ Mf, zOf e * x * (zOf e)⁻¹ ∈ Mf := fun x hx =>
    hst.compl.conj_mem (zOf e) (hEP hzE) x hx
  have htC : ∀ x ∈ Mf, t' * x * t'⁻¹ = x → x ∈ W₁ := fun x hx hxc => by
    have hc' : x ∈ Mf ⊓ Subgroup.centralizer ({t'} : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨hx, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact mul_inv_eq_iff_eq_mul.mp hxc
    rw [hst.cent_t'] at hc'
    exact hc'
  have hzC : ∀ c' ∈ Mf, zOf e * c' = c' * zOf e → c' ^ 3 = 1 := fun c' hc' hcz => by
    have hcH : c' ∈ H := (mem_H_iff_zOf hone hlet c').mpr hcz
    obtain ⟨k, hk⟩ := hst.three ⟨c', hc'⟩
    exact cube_one_of_H hF c' hcH k (congrArg Subtype.val hk)
  have hord_tz : orderOf (t' * zOf e) = 2 := by
    rcases hst.t'_mem with h1 | h1
    · rw [h1]
      exact orderOf_e4z hone hlet
    · rw [h1, mul_assoc, zOf_mul_self hone hlet, mul_one]
      exact orderOf_e4 hone hlet
  have htzC : ∀ c' ∈ Mf, (t' * zOf e) * c' = c' * (t' * zOf e) → c' ^ 3 = 1 := fun c' hc' hcu => by
    obtain ⟨c0, hc0⟩ := conj_zOf_of_orderOf hO (t' * zOf e) hord_tz
    obtain ⟨k, hk⟩ := hst.three ⟨c', hc'⟩
    exact cube_one_of_conj hone hlet hF c0 (t' * zOf e) c' hc0 hcu k (congrArg Subtype.val hk)
  have htσ : t' * σ = σ * t' := hBt σ hσB
  have hWc' : ∀ x ∈ Mf, ∀ n ∈ W₁, x * n * x⁻¹ = n := fun x hx n hn => W₁_central_Mf hst x hx n hn
  have htW : ∀ w ∈ W₁, t' * w * t'⁻¹ = w := hst.W₁_cent
  have hzW : ∀ w ∈ W₁, zOf e * w * (zOf e)⁻¹ = w⁻¹ := hst.W₁_inv
  obtain ⟨Q, hQ, hQcard⟩ := V_concrete hWc' hcomm' hWMf hst.card_Mf hst.card_W₁ hWexp ht2 hz2 hσ3
    htN hzN hσN htW hzW hσWc htC hzC htzC htσ
  exact closing_contradiction hone hlet hF hL.pb hPb B W₁ Mf Q σ g hBeq hBcomm hWc' hσMf hσ3 hσ1
    hQ hQcard (fun x hx => hg x hx)

end CFSG.GH74.QTGen4.Recog.G23.P7
