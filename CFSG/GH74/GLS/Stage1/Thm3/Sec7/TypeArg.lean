module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Ctx

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec7

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
  CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def XK (z : G) (K : Subgroup G) : Subgroup G := K ⊔ (cSec K ⊓ centralizer ({z} : Set G))

theorem cmap_eq_cj (c : G) (K : Subgroup G) : cmap c K = M.cj K c⁻¹ := by
  ext x
  rw [mem_cmap, M.mem_cj, inv_inv]

theorem cmap_of_mem {c : G} {H : Subgroup G} (hc : c ∈ H) : cmap c H = H := by
  ext x
  rw [mem_cmap]
  constructor
  · intro h
    have := H.mul_mem (H.mul_mem hc h) (H.inv_mem hc)
    have e : c * (c⁻¹ * x * c) * c⁻¹ = x := by group
    rwa [e] at this
  · intro hx
    exact H.mul_mem (H.mul_mem (H.inv_mem hc) hx) hc

theorem cmap_cSec (c : G) (K : Subgroup G) : cmap c (cSec K) = cSec (cmap c K) := by
  ext x
  rw [mem_cmap]
  constructor
  · intro hx
    have h1 := cmap_mem_centralizerSection hx c
    rw [show c * (c⁻¹ * x * c) * c⁻¹ = x by group] at h1
    show x ∈ centralizerSection (cmap c K) (pPrimeCoreOf 2 (cmap c K))
    rw [pPrimeCoreOf_cmap]
    exact h1
  · intro hx
    have hx' : x ∈ centralizerSection (cmap c K) (cmap c (pPrimeCoreOf 2 K)) := by
      rw [← pPrimeCoreOf_cmap]; exact hx
    have h1 := cmap_mem_centralizerSection hx' c⁻¹
    rw [cmap_inv_cancel, cmap_inv_cancel, inv_inv] at h1
    exact h1

theorem cmap_XK {c z : G} (hc : c ∈ centralizer ({z} : Set G)) (K : Subgroup G) :
    cmap c (XK z K) = XK z (cmap c K) := by
  have h1 : cmap c (XK z K) =
      cmap c K ⊔ (cmap c (cSec K) ⊓ cmap c (centralizer ({z} : Set G))) := by
    unfold XK
    show Subgroup.map _ (K ⊔ (cSec K ⊓ centralizer ({z} : Set G))) = _
    rw [Subgroup.map_sup, Subgroup.map_inf _ _ _ (MulAut.conj c).injective]
  rw [h1, cmap_cSec, cmap_of_mem hc]
  rfl

namespace Cfg7

variable {z : G} {S K₁ K₂ : Subgroup G} {t u : G} {q : ℕ} [Finite G]

theorem norm_both (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q) {c : G}
    (hc : c ∈ centralizer ({z} : Set G)) {K : Subgroup G} (hK : K = K₁ ∨ K = K₂)
    (hcK : c ∈ normalizer (K : Set G)) :
    c ∈ normalizer (K₁ : Set G) ∧ c ∈ normalizer (K₂ : Set G) := by
  have hM := h.m4 hII
  have hne : K₁ ≠ K₂ := h.std.std.ne
  rcases hM.perm c hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨M.cj_eq_iff_normalizer.1 h1, M.cj_eq_iff_normalizer.1 h2⟩
  · exfalso
    rcases hK with rfl | rfl
    · have := M.cj_eq_iff_normalizer.2 hcK
      rw [h1] at this
      exact hne this.symm
    · have := M.cj_eq_iff_normalizer.2 hcK
      rw [h2] at this
      exact hne this

theorem cj_mem_pair (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q) {x : G}
    (hx : x ∈ centralizer ({z} : Set G)) {K : Subgroup G} (hK : K = K₁ ∨ K = K₂) :
    M.cj K x = K₁ ∨ M.cj K x = K₂ := by
  have hM := h.m4 hII
  rcases hM.perm x hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rcases hK with rfl | rfl
    · exact Or.inl h1
    · exact Or.inr h2
  · rcases hK with rfl | rfl
    · exact Or.inr h1
    · exact Or.inl h2

theorem K_le_C (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q) {K : Subgroup G}
    (hK : K = K₁ ∨ K = K₂) : K ≤ centralizer ({z} : Set G) := by
  have hM := h.m4 hII
  rcases hK with rfl | rfl
  · exact hM.K₁_le
  · exact hM.K₂_le

theorem Hs_normal (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q) {K : Subgroup G}
    (hK : K = K₁ ∨ K = K₂) :
    ∀ x ∈ centralizer ({z} : Set G), ∀ n ∈ centralizer ({z} : Set G) ⊓ normalizer (K : Set G),
      x * n * x⁻¹ ∈ centralizer ({z} : Set G) ⊓ normalizer (K : Set G) := by
  intro x hx n hn
  have hnC : n ∈ centralizer ({z} : Set G) := hn.1
  obtain ⟨hn1, hn2⟩ := h.norm_both hII hnC hK hn.2
  refine Subgroup.mem_inf.2 ⟨(centralizer ({z} : Set G)).mul_mem
    ((centralizer ({z} : Set G)).mul_mem hx hnC) ((centralizer ({z} : Set G)).inv_mem hx), ?_⟩
  have hcj := h.cj_mem_pair hII hx hK
  have : n ∈ normalizer ((M.cj K x : Subgroup G) : Set G) := by
    rcases hcj with h1 | h1
    · rw [h1]; exact hn1
    · rw [h1]; exact hn2
  exact M.mem_normalizer_cj this

theorem inf_XK_le (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q) {K : Subgroup G}
    (hK : K = K₁ ∨ K = K₂) : ∀ y ∈ S, y ∈ XK z K → y ∈ Pof S K ⊔ Qof S K := by
  intro y hyS hyX
  have hM := h.m4 hII
  set C : Subgroup G := centralizer ({z} : Set G) with hC
  set Hs : Subgroup G := C ⊓ normalizer (K : Set G) with hHs
  set B : Subgroup G := cSec K ⊓ C with hB
  set X : Subgroup G := K ⊔ B with hXdef
  have hKC : K ≤ C := h.K_le_C hII hK
  have hBN : B ≤ normalizer (K : Set G) := fun x hx => (mem_cSec.1 hx.1).1
  have hXH : X ≤ Hs := sup_le (fun x hx => ⟨hKC hx, Subgroup.le_normalizer hx⟩)
    (fun x hx => ⟨hx.2, hBN hx⟩)
  have hXC : X ≤ C := hXH.trans inf_le_left
  have hXn : ∀ x ∈ Hs, ∀ n ∈ X, x * n * x⁻¹ ∈ X := by
    intro x hx n hn
    have hxN : x ∈ normalizer (K : Set G) := hx.2
    have hmapK : K.map (MulAut.conj x).toMonoidHom ≤ K := by
      rintro _ ⟨k, hk, rfl⟩
      exact (Subgroup.mem_normalizer_iff.1 hxN k).1 hk
    have hmapB : B.map (MulAut.conj x).toMonoidHom ≤ B := by
      rintro _ ⟨b, hb, rfl⟩
      exact Subgroup.mem_inf.2 ⟨cSec_conj K hxN hb.1,
        C.mul_mem (C.mul_mem hx.1 hb.2) (C.inv_mem hx.1)⟩
    have hmapX : X.map (MulAut.conj x).toMonoidHom ≤ X := by
      rw [hXdef, Subgroup.map_sup]
      exact sup_le (hmapK.trans le_sup_left) (hmapB.trans le_sup_right)
    exact hmapX ⟨n, hn, rfl⟩
  have hHsN : ∀ x ∈ C, ∀ n ∈ Hs, x * n * x⁻¹ ∈ Hs := h.Hs_normal hII hK
  have hS₁syl : M.Syl2In (S ⊓ Hs) Hs := hM.S_syl.inf_normal inf_le_left hHsN
  have hXsyl : M.Syl2In ((S ⊓ Hs) ⊓ X) X := hS₁syl.inf_normal hXH hXn
  have hSX : (S ⊓ Hs) ⊓ X = S ⊓ X := by
    rw [inf_assoc, inf_eq_right.2 hXH]
  rw [hSX] at hXsyl
  have hQcomm : ∀ a ∈ (S ⊓ X) ⊓ K, ∀ b ∈ (S ⊓ X) ⊓ B, a * b = b * a := by
    intro a ha b hb
    exact (h.Q_comm_P hII hK b ⟨hb.1.1, hb.2.1⟩ a ⟨ha.1.1, ha.2⟩).symm
  have hnA : ∀ x ∈ K ⊔ B, ∀ n ∈ K, x * n * x⁻¹ ∈ K := fun x hx n hn =>
    (Subgroup.mem_normalizer_iff.1 (hXH hx).2 n).1 hn
  have hnB : ∀ x ∈ K ⊔ B, ∀ n ∈ B, x * n * x⁻¹ ∈ B := fun x hx n hn =>
    Subgroup.mem_inf.2 ⟨cSec_conj K (hXH hx).2 hn.1,
      C.mul_mem (C.mul_mem (hXC hx) hn.2) (C.inv_mem (hXC hx))⟩
  have heq := M.Syl2In.eq_sup_of_normalizing hBN hnA hnB hXsyl hQcomm
  have hy : y ∈ (S ⊓ X) ⊓ K ⊔ (S ⊓ X) ⊓ B := by
    rw [← heq]; exact ⟨hyS, hyX⟩
  have h12 : (S ⊓ X) ⊓ K ⊔ (S ⊓ X) ⊓ B ≤ Pof S K ⊔ Qof S K :=
    sup_le_sup (fun x hx => ⟨hx.1.1, hx.2⟩) (fun x hx => ⟨hx.1.1, hx.2.1⟩)
  exact h12 hy

theorem mix (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q) :
    ∀ x ∈ Pof S K₁ ⊔ Qof S K₁, x ∉ Pof S K₂ ⊔ Qof S K₂ → ∀ g : G, g⁻¹ * z * g = z →
      g⁻¹ * x * g ∈ S →
      ((g⁻¹ * x * g ∈ Pof S K₁ ⊔ Qof S K₁ ∧ g⁻¹ * x * g ∉ Pof S K₂ ⊔ Qof S K₂) ∨
        (g⁻¹ * x * g ∈ Pof S K₂ ⊔ Qof S K₂ ∧ g⁻¹ * x * g ∉ Pof S K₁ ⊔ Qof S K₁)) := by
  intro x hx hxn g hgz hyS
  have hM := h.m4 hII
  have hgC : g ∈ centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * z = g * (g⁻¹ * z * g) := by rw [hgz]
      _ = z * g := by group
  have hgC' : g⁻¹ ∈ centralizer ({z} : Set G) := inv_mem hgC
  have hxS : x ∈ S := by
    have : Pof S K₁ ⊔ Qof S K₁ ≤ S := sup_le inf_le_left inf_le_left
    exact this hx
  have hPQ₁ : Pof S K₁ ⊔ Qof S K₁ ≤ XK z K₁ :=
    sup_le (fun a ha => mem_sup_left ha.2)
      (fun a ha => mem_sup_right ⟨ha.2, hM.S_syl.1 ha.1⟩)
  have hPQ₂ : Pof S K₂ ⊔ Qof S K₂ ≤ XK z K₂ :=
    sup_le (fun a ha => mem_sup_left ha.2)
      (fun a ha => mem_sup_right ⟨ha.2, hM.S_syl.1 ha.1⟩)
  have hx₁ : x ∈ XK z K₁ := hPQ₁ hx
  have hx₂ : x ∉ XK z K₂ := fun hx₂ => hxn (h.inf_XK_le hII (Or.inr rfl) x hxS hx₂)
  have key : ∀ K : Subgroup G, (g⁻¹ * x * g ∈ XK z K ↔ x ∈ XK z (cmap g K)) := by
    intro K
    rw [← cmap_XK hgC K, mem_cmap]
  have hswap : (cmap g K₁ = K₁ ∧ cmap g K₂ = K₂) ∨ (cmap g K₁ = K₂ ∧ cmap g K₂ = K₁) := by
    simp only [cmap_eq_cj]
    exact hM.perm g⁻¹ hgC'
  rcases hswap with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    have hy₁ : g⁻¹ * x * g ∈ XK z K₁ := by rw [key K₁, h1]; exact hx₁
    have hy₂ : g⁻¹ * x * g ∉ XK z K₂ := by rw [key K₂, h2]; exact hx₂
    exact ⟨h.inf_XK_le hII (Or.inl rfl) _ hyS hy₁, fun hh => hy₂ (hPQ₂ hh)⟩
  · right
    have hy₂ : g⁻¹ * x * g ∈ XK z K₂ := by rw [key K₂, h2]; exact hx₁
    have hy₁ : g⁻¹ * x * g ∉ XK z K₁ := by rw [key K₁, h1]; exact hx₂
    exact ⟨h.inf_XK_le hII (Or.inr rfl) _ hyS hy₂, fun hh => hy₁ (hPQ₁ hh)⟩

end Cfg7

end CFSG.GH74.GLS.Stage1.Thm3.Sec7
