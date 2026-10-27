module

public import CFSG.CGT.Foote81L6.Normalizer.GTvHyp
public import CFSG.CGT.Foote81L6.Normalizer.OddCentralizerCard

public section

namespace CFSG.CGT.Foote81L6.Normalizer

open Subgroup CFSG.Quasithin Equiv
open scoped IsMulCommutative

private theorem perm_involution_four : ∀ σ : Perm (Fin 4), σ * σ = 1 → σ ≠ 1 →
    (∃ τ : Perm (Fin 4), τ * swap 0 1 * τ⁻¹ = σ) ∨
      (∃ τ : Perm (Fin 4), τ * (swap 0 1 * swap 2 3) * τ⁻¹ = σ) := by
  decide +kernel

private theorem perm_involution_five : ∀ σ : Perm (Fin 5), σ * σ = 1 → σ ≠ 1 →
    (∃ τ : Perm (Fin 5), τ * swap 0 1 * τ⁻¹ = σ) ∨
      (∃ τ : Perm (Fin 5), τ * (swap 0 1 * swap 2 3) * τ⁻¹ = σ) := by
  decide +kernel

theorem perm_involution {m : ℕ} [NeZero m] (hm : m = 4 ∨ m = 5) :
    ∀ σ : Perm (Fin m), σ * σ = 1 → σ ≠ 1 →
      (∃ τ : Perm (Fin m), τ * swap 0 1 * τ⁻¹ = σ) ∨
        (∃ τ : Perm (Fin m), τ * (swap 0 1 * swap 2 3) * τ⁻¹ = σ) := by
  rcases hm with rfl | rfl
  · exact perm_involution_four
  · exact perm_involution_five

theorem perm_four_card_centralizer :
    (Finset.univ.filter fun σ : Perm (Fin 4) =>
      σ * (swap 0 1 * swap 2 3) = swap 0 1 * swap 2 3 * σ).card = 8 := by
  decide +kernel

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {n : ℕ}
  (D : FooteCore G (T : Subgroup G) 2 n) {F : Subgroup G} (hF : IsE64 (T : Subgroup G) F)
  [IsMulCommutative ↥F]

include hF in
theorem card_fixV_eq (u : ↥(normalizer (F : Set G))) :
    Nat.card ↥(fixV (zpowers (NBar.ρ F (NBar.π F u)))) =
      Nat.card ↥(F ⊓ centralizer ({(u : G)} : Set G)) := by
  have hmap : (fixV (zpowers (NBar.ρ F (NBar.π F u)))).map F.subtype =
      F ⊓ centralizer ({(u : G)} : Set G) := by
    ext g
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hw' : w ∈ fixV (zpowers (NBar.ρ F (NBar.π F u))) := hw
      rw [mem_fixV_zpowers_iff_apply, ρ_π_eq_self_iff] at hw'
      refine mem_inf.2 ⟨w.2, mem_centralizer_singleton_iff.2 ?_⟩
      calc (w : G) * u = ((u : G) * w * (u : G)⁻¹) * u := by rw [hw']
        _ = u * w := by group
    · rintro ⟨hgF, hgc⟩
      refine ⟨⟨g, hgF⟩, ?_, rfl⟩
      show _ ∈ fixV _
      rw [mem_fixV_zpowers_iff_apply, ρ_π_eq_self_iff]
      show (u : G) * g * (u : G)⁻¹ = g
      rw [← mem_centralizer_singleton_iff.1 hgc, mul_inv_cancel_right]
  rw [← hmap, card_map_of_injective F.subtype_injective]

variable {d₀ d₁ : G}
  (hd₀ : d₀ ∈ D.B₀ ⊓ normalizer ((F ⊓ D.B₀ : Subgroup G) : Set G)) (hd₀F : d₀ ∉ F)
  (hd₁ : d₁ ∈ D.B₁ ⊓ normalizer ((F ⊓ D.B₁ : Subgroup G) : Set G)) (hd₁F : d₁ ∉ F)

include hF hd₀F hd₁F

theorem sixteen_le_card_fix {y : NBar.Q F}
    (hy : ∀ w : ↥F, NBar.ρ F (NBar.π F ⟨d₀, D.mem_normalizer_of_mem_R₀ hF hd₀⟩) w = w →
      NBar.ρ F (NBar.π F ⟨d₁, D.mem_normalizer_of_mem_R₁ hF hd₁⟩) w = w → NBar.ρ F y w = w)
    (g : NBar.Q F) : 16 ≤ Nat.card ↥(fixV (zpowers (NBar.ρ F (g * y * g⁻¹)))) := by
  haveI := hF.finite
  set W := fixV (zpowers (NBar.ρ F (NBar.π F ⟨d₀, D.mem_normalizer_of_mem_R₀ hF hd₀⟩))) ⊓
    fixV (zpowers (NBar.ρ F (NBar.π F ⟨d₁, D.mem_normalizer_of_mem_R₁ hF hd₁⟩))) with hW
  have hcard : Nat.card W = 16 := card_fix_d₀_d₁ D hF hd₀ hd₀F hd₁ hd₁F
  have hle : W.map (NBar.ρ F g).toMonoidHom ≤ fixV (zpowers (NBar.ρ F (g * y * g⁻¹))) := by
    rintro _ ⟨w, hw, rfl⟩
    have hw' : w ∈ W := hw
    rw [hW, mem_inf, mem_fixV_zpowers_iff_apply, mem_fixV_zpowers_iff_apply] at hw'
    rw [mem_fixV_zpowers_iff_apply]
    simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv, MulAut.mul_apply, MulAut.inv_apply,
      MulEquiv.symm_apply_apply]
    rw [hy w hw'.1 hw'.2]
  calc 16 = Nat.card ↥(W.map (NBar.ρ F g).toMonoidHom) := by
        rw [card_map_of_injective (NBar.ρ F g).injective, hcard]
    _ ≤ _ := Subgroup.card_le_of_le hle

variable {m : ℕ} [NeZero m] (hm : m = 4 ∨ m = 5) {φ : NBar.Q F →* Perm (Fin m)}
  (hφ : IsSymDirect (NBar.π F ⟨d₀, D.mem_normalizer_of_mem_R₀ hF hd₀⟩)
    (NBar.π F ⟨d₁, D.mem_normalizer_of_mem_R₁ hF hd₁⟩) φ)
  (hO : pPrimeCore 2 (NBar.Q F) = ⊥)

include hm hφ hO in
theorem not_isFree_involution {t' : G} (ht' : t' ∈ (T : Subgroup G) ⊓ normalizer (F : Set G))
    (ht'2 : t' * t' = 1) (ht'0 : t' ∉ D.T₀) : False := by
  set t'N : ↥(normalizer (F : Set G)) := ⟨t', (mem_inf.1 ht').2⟩
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, hφ.ker_eq, hO]
  have ht'F : t' ∉ F := fun h => ht'0 (D.T₁_le_T₀ (D.le_T₁_of_isE64 hF h))
  have h8 : Nat.card ↥(fixV (zpowers (NBar.ρ F (NBar.π F t'N)))) = 8 := by
    rw [card_fixV_eq hF]
    exact D.card_centralizer_E64_of_not_mem_T₀ rfl hF (mem_inf.1 ht').1 (mem_inf.1 ht').2 ht'0
      ht'2
  have hsq : φ (NBar.π F t'N) * φ (NBar.π F t'N) = 1 := by
    rw [← map_mul, ← map_mul, show t'N * t'N = 1 from Subtype.ext ht'2, map_one, map_one]
  have hne : φ (NBar.π F t'N) ≠ 1 := by
    intro h
    have h1 : NBar.π F t'N = 1 := hφinj (h.trans (map_one φ).symm)
    exact ρ_ne_one_of_not_mem D hF t'N (mem_inf.1 ht').1 ht'F (by rw [h1, map_one])
  set d₀b := NBar.π F ⟨d₀, D.mem_normalizer_of_mem_R₀ hF hd₀⟩
  set d₁b := NBar.π F ⟨d₁, D.mem_normalizer_of_mem_R₁ hF hd₁⟩
  obtain ⟨htv₀, -⟩ := isTransvectionWith_d₀ D hF hd₀ hd₀F
  obtain ⟨htv₁, hd₁1⟩ := isTransvectionWith_d₁ D hF hd₁ hd₁F
  rcases perm_involution hm _ hsq hne with ⟨τ, hτ⟩ | ⟨τ, hτ⟩
  · obtain ⟨g, rfl⟩ := hφ.surjective τ
    have heq : NBar.π F t'N = g * d₀b * g⁻¹ :=
      hφinj (by rw [map_mul, map_mul, map_inv, hφ.map₀, hτ])
    have h16 := sixteen_le_card_fix D hF hd₀ hd₀F hd₁ hd₁F (y := d₀b) (fun w h0 _ => h0) g
    rw [← heq, h8] at h16
    omega
  · obtain ⟨g, rfl⟩ := hφ.surjective τ
    have heq : NBar.π F t'N = g * (d₀b * d₁b) * g⁻¹ :=
      hφinj (by rw [map_mul, map_mul, map_inv, map_mul, hφ.map₀, hφ.map₁, hτ])
    have h16 := sixteen_le_card_fix D hF hd₀ hd₀F hd₁ hd₁F (y := d₀b * d₁b)
      (fun w h0 h1 => by rw [map_mul, MulAut.mul_apply, h1, h0]) g
    rw [← heq, h8] at h16
    omega

include hm hφ hO in
theorem mem_T₀_of_isSymDirect {x : G} (hx : x ∈ (T : Subgroup G) ⊓ normalizer (F : Set G)) :
    x ∈ D.T₀ := by
  by_contra hx0
  by_cases hsym : (D.typ F).1 = (D.typ F).2
  · exact hx0 (D.mem_T₀_of_mem_normalizer_of_symm hF hsym (mem_inf.1 hx).1 (mem_inf.1 hx).2)
  · obtain ⟨t', ht', ht'2, ht't⟩ := D.exists_tprime_of_asymm rfl hF hsym
    refine not_isFree_involution D hF hd₀ hd₀F hd₁ hd₁F hm hφ hO ht' ht'2 fun h => ?_
    apply D.t_not_mem_T₀
    have : D.t = (t' * D.t⁻¹)⁻¹ * t' := by group
    rw [this]
    exact mul_mem (inv_mem (D.T₁_le_T₀ ht't)) h

include hm hφ hO in
theorem ne_map_Frep01 :
    ∀ h ∈ (T : Subgroup G), F ≠ (D.Frep 0 1).map (MulAut.conj h).toMonoidHom := by
  intro h hh hFh
  obtain ⟨t', ht', ht'2, ht't⟩ := D.exists_tprime rfl ⟨h, hh, hFh⟩
  refine not_isFree_involution D hF hd₀ hd₀F hd₁ hd₁F hm hφ hO ht' ht'2 fun h0 => ?_
  apply D.t_not_mem_T₀
  have : D.t = (t' * D.t⁻¹)⁻¹ * t' := by group
  rw [this]
  exact mul_mem (inv_mem (D.T₁_le_T₀ ht't)) h0

include hm hφ hO in
theorem fix_of_sym_four {Q : Sylow 2 ↥(normalizer (F : Set G))}
    (hQ : (Q : Subgroup _) = (T : Subgroup G).subgroupOf (normalizer (F : Set G)))
    (hDz : ∀ c ∈ (NBar.sylowImage F Q : Subgroup (NBar.Q F)),
      c * (NBar.π F ⟨d₀, D.mem_normalizer_of_mem_R₀ hF hd₀⟩ *
        NBar.π F ⟨d₁, D.mem_normalizer_of_mem_R₁ hF hd₁⟩) =
      NBar.π F ⟨d₀, D.mem_normalizer_of_mem_R₀ hF hd₀⟩ *
        NBar.π F ⟨d₁, D.mem_normalizer_of_mem_R₁ hF hd₁⟩ * c)
    (hcard : Nat.card ↥(NBar.sylowImage F Q : Subgroup (NBar.Q F)) = 8)
    {M : Subgroup (NBar.Q F)} (hDM : (NBar.sylowImage F Q : Subgroup (NBar.Q F)) ≤ M)
    (ψ : M ≃* Perm (Fin 4)) :
    ∀ g ∈ M, ∀ v : ↥F, (v : G) ∈ D.A ⊔ zpowers D.b → NBar.ρ F g v = v := by
  classical
  set d₀N : ↥(normalizer (F : Set G)) := ⟨d₀, D.mem_normalizer_of_mem_R₀ hF hd₀⟩
  set d₁N : ↥(normalizer (F : Set G)) := ⟨d₁, D.mem_normalizer_of_mem_R₁ hF hd₁⟩
  set z := NBar.π F d₀N * NBar.π F d₁N with hz
  have hd₀T : d₀ ∈ (T : Subgroup G) := D.B_le_T (D.B₀_le_B (mem_inf.1 hd₀).1)
  have hd₁T : d₁ ∈ (T : Subgroup G) := D.B_le_T (D.B₁_le_B (mem_inf.1 hd₁).1)
  have hM₀ : NBar.π F d₀N ∈ M := hDM (π_mem_sylowImage hQ d₀N hd₀T)
  have hM₁ : NBar.π F d₁N ∈ M := hDM (π_mem_sylowImage hQ d₁N hd₁T)
  obtain ⟨u, huM, -, -, hu_comm, hfix⟩ := hφ.sym_four_fixes hm hM₀ hM₁ ψ
  obtain ⟨ψ', hψ₀, hψ₁⟩ := hφ.exists_normalized_four hm hM₀ hM₁ ψ
  have hψz : ψ' ⟨z, M.mul_mem hM₀ hM₁⟩ = swap 0 1 * swap 2 3 := by
    rw [show (⟨z, M.mul_mem hM₀ hM₁⟩ : M) = ⟨NBar.π F d₀N, hM₀⟩ * ⟨NBar.π F d₁N, hM₁⟩ from rfl,
      map_mul, hψ₀, hψ₁]
  set C := M ⊓ centralizer ({z} : Set (NBar.Q F)) with hC
  have hDC : (NBar.sylowImage F Q : Subgroup (NBar.Q F)) ≤ C := fun c hc =>
    mem_inf.2 ⟨hDM hc, mem_centralizer_singleton_iff.2 (hDz c hc)⟩
  have hC8 : Nat.card C ≤ 8 := by
    let f : C → {σ : Perm (Fin 4) // σ * (swap 0 1 * swap 2 3) = swap 0 1 * swap 2 3 * σ} :=
      fun c => ⟨ψ' ⟨c, (mem_inf.1 c.2).1⟩, by
        rw [← hψz, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (mem_centralizer_singleton_iff.1 (mem_inf.1 c.2).2)⟩
    have hf : Function.Injective f := fun c c' h => by
      have h1 := ψ'.injective (congrArg Subtype.val h)
      exact Subtype.ext (by simpa using congrArg Subtype.val h1)
    have h2 := Nat.card_le_card_of_injective f hf
    have h8 : Nat.card {σ : Perm (Fin 4) // σ * (swap 0 1 * swap 2 3) =
        swap 0 1 * swap 2 3 * σ} = 8 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype, perm_four_card_centralizer]
    exact h2.trans h8.le
  have hDeq : (NBar.sylowImage F Q : Subgroup (NBar.Q F)) = C :=
    eq_of_le_of_card_ge hDC (by rw [hcard]; exact hC8)
  have huD : u ∈ (NBar.sylowImage F Q : Subgroup (NBar.Q F)) := by
    rw [hDeq]
    exact mem_inf.2 ⟨huM, mem_centralizer_singleton_iff.2 hu_comm⟩
  rw [NBar.coe_sylowImage] at huD
  obtain ⟨u₀, hu₀Q, rfl⟩ := huD
  have hu₀T : (u₀ : G) ∈ (T : Subgroup G) := by
    have h : u₀ ∈ (Q : Subgroup ↥(normalizer (F : Set G))) := hu₀Q
    rw [hQ, mem_subgroupOf] at h
    exact h
  have hu₀T₀ := mem_T₀_of_isSymDirect D hF hd₀ hd₀F hd₁ hd₁F hm hφ hO (mem_inf.2 ⟨hu₀T, u₀.2⟩)
  have hu₀c : ∀ x ∈ D.A ⊔ zpowers D.b, (u₀ : G) * x = x * u₀ := by
    have hle : D.A ⊔ zpowers D.b ≤ centralizer ({(u₀ : G)} : Set G) := by
      refine sup_le (fun x hx => mem_centralizer_singleton_iff.2 ?_)
        (zpowers_le.2 (mem_centralizer_singleton_iff.2 (D.b_comm_T hu₀T).symm))
      obtain ⟨α, hα, β, hβ, hαβ⟩ := D.mem_T₀_iff.1 hu₀T₀
      rw [hαβ]
      calc x * (α * β) = α * (x * β) := by rw [← mul_assoc, D.A_comm_of_two hx hα, mul_assoc]
        _ = α * β * x := by rw [D.A_comm_B x hx β hβ, mul_assoc]
    exact fun x hx => (mem_centralizer_singleton_iff.1 (hle hx)).symm
  obtain ⟨htv₀, hd₀1⟩ := isTransvectionWith_d₀ D hF hd₀ hd₀F
  obtain ⟨htv₁, hd₁1⟩ := isTransvectionWith_d₁ D hF hd₁ hd₁F
  have hb : (⟨D.b₀, D.b₀_mem_E64 hF⟩ : ↥F) ≠ ⟨D.b₁, D.b₁_mem_E64 hF⟩ := by
    intro h'
    have hb' : D.b₀ = D.b₁ := congrArg Subtype.val h'
    have : D.b₀ ∈ D.B₀ ⊓ D.B₁ := mem_inf.2 ⟨D.b₀_mem, hb' ▸ D.b₁_mem⟩
    rw [D.B₀_inf_B₁, mem_bot] at this
    exact D.b₀_ne_one this
  have hcomm₀₁ : NBar.π F d₀N * NBar.π F d₁N = NBar.π F d₁N * NBar.π F d₀N :=
    hφ.commute₀₁ hm
  have hV : ∀ w : ↥F, w * w = 1 := fun w => Subtype.ext (hF.mul_self w w.2)
  have hfix' := hfix (NBar.ρ F) (fun w hw _ =>
    ((fix_mul_iff hV htv₀ htv₁ hd₁1 hb hcomm₀₁ w).1 hw).1)
  intro g hg v hv
  have hvZ : (v : G) ∈ D.A ⊔ (zpowers D.b₀ ⊔ zpowers D.b₁) := by
    refine sup_le le_sup_left (zpowers_le.2 ?_) hv
    exact mem_sup_right (mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right (mem_zpowers _)))
  obtain ⟨h0, h1⟩ := (fix_iff_mem_Z D hF hd₀ hd₀F hd₁ hd₁F v).2 hvZ
  refine hfix' g hg v ((fix_mul_iff hV htv₀ htv₁ hd₁1 hb hcomm₀₁ v).2 ⟨h0, h1⟩) ?_
  rw [ρ_π_eq_self_iff, hu₀c v hv, mul_inv_cancel_right]

end CFSG.CGT.Foote81L6.Normalizer
