module

public import CFSG.Quasithin.Background.SmithC27RLieA6
public import CFSG.Permutation.FinPackEven6
public import CFSG.Permutation.FinPackComm

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KPGenK

open CFSG.Permutation.FinPack CFSG.Quasithin.SmithC27 Equiv

@[expose] noncomputable def nrmK (T : ℕ) (VK : List ℕ) (p : ℕ) : Bool :=
  !commLaneK 6 (lo6 p) T || allK (fun v => memK (mulK 6 (mulK 6 (lo6 p) v) (hi6 p)) VK) VK

theorem conj_mem_of_nrm {T : ℕ} {VK : List ℕ} {VL : List (Perm (Fin 6))} (hV : VL.map enc = VK)
    {t : Perm (Fin 6)} (hT : enc t = T) (h : allK (nrmK T VK) evenCodes6 = true)
    {σ : Perm (Fin 6)} (hσ : Perm.sign σ = 1) (hc : σ * t = t * σ) {v : Perm (Fin 6)}
    (hv : v ∈ VL) : σ * v * σ⁻¹ ∈ VL := by
  have h1 := allK_iff.1 h _ (memK_iff.1 (pc6_mem_even σ hσ))
  unfold nrmK at h1
  rw [lo6_pc6, hi6_pc6, ← hT, (commLaneK_iff (by norm_num) σ t).2 hc, Bool.not_true,
    Bool.false_or] at h1
  have hv' : enc v ∈ VK := by
    rw [← hV]
    exact List.mem_map_of_mem hv
  have h2 := memK_iff.1 (allK_iff.1 h1 _ hv')
  rw [← enc_mul (n := 6) (by norm_num), ← enc_mul (n := 6) (by norm_num), ← hV] at h2
  exact (mem_iff_enc (by norm_num) VL _).2 h2

@[expose] def v1K : List ℕ := [0x543210, 0x542301, 0x541032, 0x540123]

@[expose] def v2K : List ℕ := [0x543210, 0x542301, 0x453201, 0x452310]

@[expose] def invK6 : ℕ := 0x542301

theorem pin_v1 : ([1, (alt6Inv : Perm (Fin 6)), (alt6InvA : Perm (Fin 6)),
    (alt6InvC : Perm (Fin 6))] : List (Perm (Fin 6))).map enc = v1K := by
  decide +kernel

theorem pin_v2 : ([1, (alt6Inv : Perm (Fin 6)), (alt6InvB : Perm (Fin 6)),
    (alt6InvD : Perm (Fin 6))] : List (Perm (Fin 6))).map enc = v2K := by
  decide +kernel

theorem pin_inv : enc (alt6Inv : Perm (Fin 6)) = invK6 := by decide +kernel

theorem nrm1 : allK (nrmK invK6 v1K) evenCodes6 = true := by decide +kernel

theorem nrm2 : allK (nrmK invK6 v2K) evenCodes6 = true := by decide +kernel

theorem mem4_iff {x a b c d : ↥(alternatingGroup (Fin 6))} :
    (x = a ∨ x = b ∨ x = c ∨ x = d) ↔
      (x : Perm (Fin 6)) ∈ ([(a : Perm (Fin 6)), b, c, d] : List (Perm (Fin 6))) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, Subtype.ext_iff]

theorem fwd_of {L : List (Perm (Fin 6))} {VK : List ℕ} (hV : L.map enc = VK)
    (h : allK (nrmK invK6 VK) evenCodes6 = true) {a b c : ↥(alternatingGroup (Fin 6))}
    (hL : L = [((1 : ↥(alternatingGroup (Fin 6))) : Perm (Fin 6)), a, b, c])
    (g : ↥(alternatingGroup (Fin 6))) (hg : g * alt6Inv = alt6Inv * g) (x : ↥(alternatingGroup (Fin 6)))
    (hx : x = 1 ∨ x = a ∨ x = b ∨ x = c) :
    g * x * g⁻¹ = 1 ∨ g * x * g⁻¹ = a ∨ g * x * g⁻¹ = b ∨ g * x * g⁻¹ = c := by
  rw [mem4_iff, ← hL] at hx ⊢
  have hc : (g : Perm (Fin 6)) * alt6Inv = alt6Inv * g := congrArg Subtype.val hg
  have hs : Perm.sign (g : Perm (Fin 6)) = 1 := Perm.mem_alternatingGroup.1 g.2
  exact conj_mem_of_nrm hV pin_inv h hs hc hx

theorem fwd_V1 (g : ↥(alternatingGroup (Fin 6))) (hg : g * alt6Inv = alt6Inv * g)
    (x : ↥(alternatingGroup (Fin 6))) (hx : x = 1 ∨ x = alt6Inv ∨ x = alt6InvA ∨ x = alt6InvC) :
    g * x * g⁻¹ = 1 ∨ g * x * g⁻¹ = alt6Inv ∨ g * x * g⁻¹ = alt6InvA ∨ g * x * g⁻¹ = alt6InvC :=
  fwd_of pin_v1 nrm1 rfl g hg x hx

theorem fwd_V2 (g : ↥(alternatingGroup (Fin 6))) (hg : g * alt6Inv = alt6Inv * g)
    (x : ↥(alternatingGroup (Fin 6))) (hx : x = 1 ∨ x = alt6Inv ∨ x = alt6InvB ∨ x = alt6InvD) :
    g * x * g⁻¹ = 1 ∨ g * x * g⁻¹ = alt6Inv ∨ g * x * g⁻¹ = alt6InvB ∨ g * x * g⁻¹ = alt6InvD :=
  fwd_of pin_v2 nrm2 rfl g hg x hx

theorem iff_of_fwd {G : Type*} [Group G] {P : G → Prop} {g : G} (h1 : ∀ x, P x → P (g * x * g⁻¹))
    (h2 : ∀ x, P x → P (g⁻¹ * x * g⁻¹⁻¹)) (x : G) : P x ↔ P (g * x * g⁻¹) := by
  refine ⟨h1 x, fun hx => ?_⟩
  have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  rw [← e]
  exact h2 _ hx

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KPGenK
