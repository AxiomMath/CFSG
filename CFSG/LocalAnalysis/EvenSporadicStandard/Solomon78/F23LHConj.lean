module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.F23LHW
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Open

section WSupConj

variable {G : Type*} [Group G]

theorem wsup_conj_apply (g x : G) : (MulAut.conj g).toMonoidHom x = g * x * g⁻¹ := rfl

theorem wsup_mem_map_conj {H : Subgroup G} {g x : G} :
    x ∈ H.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ H := by
  rw [mem_map_equiv, MulAut.conj_symm_apply]

theorem wsup_isElemAbelian_mono {p : ℕ} {E F : Subgroup G} (hE : IsElemAbelian p E)
    (hFE : F ≤ E) : IsElemAbelian p F := CFSG.Open.IsElemAbelian.mono hE hFE

theorem wsup_isElemAbelian_map {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E) {H : Type*}
    [Group H] (f : G →* H) : IsElemAbelian p (E.map f) := CFSG.Open.IsElemAbelian.map hE _

theorem wsup_mem_normalizer_of_map_eq {W : Subgroup G} {g y : G}
    (hmap : W.map (MulAut.conj y).toMonoidHom = W.map (MulAut.conj g).toMonoidHom) :
    y⁻¹ * g ∈ normalizer (W : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  have h1 : g * x * g⁻¹ ∈ W.map (MulAut.conj g).toMonoidHom ↔ x ∈ W := by
    rw [wsup_mem_map_conj, show g⁻¹ * (g * x * g⁻¹) * g = x by group]
  have h2 : g * x * g⁻¹ ∈ W.map (MulAut.conj y).toMonoidHom ↔ y⁻¹ * (g * x * g⁻¹) * y ∈ W :=
    wsup_mem_map_conj
  have h3 : y⁻¹ * g * x * (y⁻¹ * g)⁻¹ = y⁻¹ * (g * x * g⁻¹) * y := by group
  rw [h3, ← h2, hmap, h1]

variable {L WL : Subgroup G} {t : G}

theorem wsup_hyp_conj (h : WSupHyp L WL t) {g s : G} (hgs : g * t * g⁻¹ = s) {A : Subgroup G}
    (hA : A ≤ L.map (MulAut.conj g).toMonoidHom) :
    WSupHyp (L.map (MulAut.conj g).toMonoidHom) A s where
  t_mem := by
    refine mem_centralizer_iff.2 ?_
    rintro _ ⟨l, hl, rfl⟩
    have hlt : l * t = t * l := mem_centralizer_iff.1 h.t_mem l hl
    rw [wsup_conj_apply, ← hgs]
    calc g * l * g⁻¹ * (g * t * g⁻¹) = g * (l * t) * g⁻¹ := by group
      _ = g * (t * l) * g⁻¹ := by rw [hlt]
      _ = g * t * g⁻¹ * (g * l * g⁻¹) := by group
  t_sq := by
    rw [← hgs]
    calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [h.t_sq]; group
  t_ne := by
    rintro rfl
    exact h.t_ne (by simpa using hgs)
  disjoint := by
    have hd := disjoint_map (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective h.disjoint
    rwa [MonoidHom.map_zpowers, wsup_conj_apply, hgs] at hd
  le := hA

theorem wsup_centralizer_conj_le (hC : centralizer ({t} : Set G) = L ⊔ zpowers t) {g s : G}
    (hgs : g * t * g⁻¹ = s) :
    centralizer ({s} : Set G) ≤ L.map (MulAut.conj g).toMonoidHom ⊔ zpowers s := by
  intro x hx
  have hxs : x * s = s * x := mem_centralizer_singleton_iff.1 hx
  have ht : t = g⁻¹ * s * g := by rw [← hgs]; group
  have hx' : g⁻¹ * x * g ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc g⁻¹ * x * g * t = g⁻¹ * (x * s) * g := by rw [ht]; group
      _ = g⁻¹ * (s * x) * g := by rw [hxs]
      _ = t * (g⁻¹ * x * g) := by rw [ht]; group
  rw [hC] at hx'
  have := wsup_mem_map_conj.2 hx'
  rwa [Subgroup.map_sup, MonoidHom.map_zpowers, wsup_conj_apply, hgs] at this

theorem wsup_eq_inf_sup {Lg V : Subgroup G} {s : G} (hs : s ∈ centralizer (Lg : Set G))
    (hC : centralizer ({s} : Set G) ≤ Lg ⊔ zpowers s) (hVC : V ≤ centralizer ({s} : Set G))
    (hsV : s ∈ V) : V = (V ⊓ Lg) ⊔ zpowers s := by
  refine le_antisymm (fun x hx => ?_) (sup_le inf_le_left (zpowers_le.2 hsV))
  obtain ⟨l, hl, b, hb, rfl⟩ :=
    exists_mul_of_mem_sup_of_le_centralizer (zpowers_le.2 hs) (hC (hVC hx))
  have hbV : b ∈ V := zpowers_le.2 hsV hb
  have hlV : l ∈ V := by simpa using mul_mem hx (inv_mem hbV)
  exact mul_mem_sup (mem_inf.2 ⟨hlV, hl⟩) hb

theorem WSupHyp.exists_mem_normalizer_of_fusion (h : WSupHyp L WL t)
    (hC : centralizer ({t} : Set G) = L ⊔ zpowers t)
    (hab : IsElemAbelian 2 WL) (hcard : Nat.card WL = 2 ^ 11) {u g : G} (huW : u ∈ WL)
    (hg : g * t * g⁻¹ = t * u)
    (hconj : ∀ A A' : Subgroup G, A ≤ L.map (MulAut.conj g).toMonoidHom →
      A' ≤ L.map (MulAut.conj g).toMonoidHom → IsElemAbelian 2 A → IsElemAbelian 2 A' →
      Nat.card A = 2 ^ 11 → Nat.card A' = 2 ^ 11 →
        ∃ y ∈ L.map (MulAut.conj g).toMonoidHom, A' = A.map (MulAut.conj y).toMonoidHom) :
    ∃ n ∈ normalizer ((WL ⊔ zpowers t : Subgroup G) : Set G), n * t * n⁻¹ = t * u := by
  set Lg := L.map (MulAut.conj g).toMonoidHom with hLgdef
  set W : Subgroup G := WL ⊔ zpowers t with hWdef
  set W' : Subgroup G := W.map (MulAut.conj g).toMonoidHom with hW'def
  have hWab : IsElemAbelian 2 W := h.isElemAbelian hab
  have hWcard : Nat.card W = 2 * 2 ^ 11 := by rw [hWdef, h.card, hcard]
  have htW : t ∈ W := mem_sup_right (mem_zpowers t)
  have hsW : t * u ∈ W := mul_mem htW (mem_sup_left huW)
  have hsW' : t * u ∈ W' := ⟨t, htW, hg⟩
  have hW'ab : IsElemAbelian 2 W' := wsup_isElemAbelian_map hWab _
  have hW'card : Nat.card W' = 2 * 2 ^ 11 := by
    rw [hW'def, card_map_of_injective (MulAut.conj g).injective, hWcard]
  have hsLg : t * u ∈ centralizer (Lg : Set G) := (wsup_hyp_conj h hg le_rfl).t_mem
  have hCs := wsup_centralizer_conj_le hC hg
  have hcentral : ∀ V : Subgroup G, IsElemAbelian 2 V → t * u ∈ V → V ≤ centralizer {t * u} :=
    fun V hV hsV x hx =>
      mem_centralizer_singleton_iff.2 ((wsup_isElemAbelian_iff.1 hV).1 x hx _ hsV)
  have hWdec := wsup_eq_inf_sup hsLg hCs (hcentral _ hWab hsW) hsW
  have hW'dec := wsup_eq_inf_sup hsLg hCs (hcentral _ hW'ab hsW') hsW'
  have hAcard : Nat.card (W ⊓ Lg : Subgroup G) = 2 ^ 11 := by
    have := (wsup_hyp_conj h hg (inf_le_right : W ⊓ Lg ≤ Lg)).card
    rw [← hWdec, hWcard] at this
    omega
  have hA'card : Nat.card (W' ⊓ Lg : Subgroup G) = 2 ^ 11 := by
    have := (wsup_hyp_conj h hg (inf_le_right : W' ⊓ Lg ≤ Lg)).card
    rw [← hW'dec, hW'card] at this
    omega
  obtain ⟨y, hyLg, hy⟩ := hconj (W ⊓ Lg) (W' ⊓ Lg) inf_le_right inf_le_right
    (wsup_isElemAbelian_mono hWab inf_le_left) (wsup_isElemAbelian_mono hW'ab inf_le_left)
    hAcard hA'card
  have hys : y * (t * u) = t * u * y := mem_centralizer_iff.1 hsLg y hyLg
  have hys' : y * (t * u) * y⁻¹ = t * u := by rw [hys]; group
  have hzp : (zpowers (t * u)).map (MulAut.conj y).toMonoidHom = zpowers (t * u) := by
    rw [MonoidHom.map_zpowers, wsup_conj_apply, hys']
  have hmap : W.map (MulAut.conj y).toMonoidHom = W' :=
    calc W.map (MulAut.conj y).toMonoidHom
        = ((W ⊓ Lg) ⊔ zpowers (t * u)).map (MulAut.conj y).toMonoidHom := by rw [← hWdec]
      _ = (W ⊓ Lg).map (MulAut.conj y).toMonoidHom ⊔
          (zpowers (t * u)).map (MulAut.conj y).toMonoidHom := Subgroup.map_sup _ _ _
      _ = (W' ⊓ Lg) ⊔ zpowers (t * u) := by rw [← hy, hzp]
      _ = W' := hW'dec.symm
  refine ⟨y⁻¹ * g, wsup_mem_normalizer_of_map_eq hmap, ?_⟩
  calc y⁻¹ * g * t * (y⁻¹ * g)⁻¹ = y⁻¹ * (g * t * g⁻¹) * y := by group
    _ = y⁻¹ * (t * u) * y := by rw [hg]
    _ = t * u := by rw [mul_assoc, ← hys]; group

end WSupConj

end CFSG.EvenSporadicStandard.Solomon78
