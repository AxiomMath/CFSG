module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S2A2

public section

namespace CFSG.QuasithinUnique.A5.S2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.AppC Equiv
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

section Alt

variable {L' : Subgroup G}

theorem le_of_alt_le_im (P : A5Pi L') {K : Subgroup G} (hKL : K ≤ L')
    (hQ : pCoreOf 2 L' ≤ K) (hA : alternatingGroup (Fin 5) ≤ P.im K) : L' ≤ K := by
  intro l hl
  have hmemA : ((P.α ⟨l, hl⟩ : alternatingGroup (Fin 5)) : Perm (Fin 5)) ∈ P.im K :=
    hA (P.α ⟨l, hl⟩).2
  obtain ⟨y, hy, hpy⟩ := (P.mem_im_pf (hKL.trans Subgroup.le_normalizer)).1 hmemA
  have hyL : y ∈ L' := hKL hy
  rw [P.pf_eq (Subgroup.le_normalizer hyL), P.hπα y hyL] at hpy
  have hαeq : P.α ⟨y, hyL⟩ = P.α ⟨l, hl⟩ := Subtype.ext hpy
  have hw : (⟨y⁻¹ * l, L'.mul_mem (L'.inv_mem hyL) hl⟩ : ↥L') ∈ P.α.ker := by
    rw [MonoidHom.mem_ker]
    have : (⟨y⁻¹ * l, L'.mul_mem (L'.inv_mem hyL) hl⟩ : ↥L') = (⟨y, hyL⟩ : ↥L')⁻¹ * ⟨l, hl⟩ := rfl
    rw [this, map_mul, map_inv, hαeq, inv_mul_cancel]
  rw [P.hαk] at hw
  have hwQ : y⁻¹ * l ∈ pCoreOf 2 L' :=
    (C56.mem_blockQ_iff (⟨y⁻¹ * l, L'.mul_mem (L'.inv_mem hyL) hl⟩ : ↥L')).2 hw
  have : l = y * (y⁻¹ * l) := by group
  rw [this]
  exact K.mul_mem hy (hQ hwQ)

end Alt

def Data.Y₂ {t : G} (h : Data T M H S L t) : Subgroup G where
  carrier := {z | z ∈ cj t L ∧ ∃ ℓ ∈ L, ℓ * z ∈ M ⊓ conjJoin S L}
  mul_mem' := by
    rintro a b ⟨ha, ℓ, hℓ, haX⟩ ⟨hb, ℓ', hℓ', hbX⟩
    refine ⟨mul_mem ha hb, ℓ * ℓ', mul_mem hℓ hℓ', ?_⟩
    have hc : ℓ' * a = a * ℓ' := h.comm_elem ℓ' hℓ' a ha
    have e : ℓ * ℓ' * (a * b) = (ℓ * a) * (ℓ' * b) :=
      calc ℓ * ℓ' * (a * b) = ℓ * (ℓ' * a) * b := by group
        _ = ℓ * (a * ℓ') * b := by rw [hc]
        _ = (ℓ * a) * (ℓ' * b) := by group
    rw [e]
    exact mul_mem haX hbX
  one_mem' := ⟨one_mem _, 1, one_mem _, by simp⟩
  inv_mem' := by
    rintro a ⟨ha, ℓ, hℓ, haX⟩
    refine ⟨inv_mem ha, ℓ⁻¹, inv_mem hℓ, ?_⟩
    have hc : ℓ * a = a * ℓ := h.comm_elem ℓ hℓ a ha
    have e : ℓ⁻¹ * a⁻¹ = (ℓ * a)⁻¹ := by
      calc ℓ⁻¹ * a⁻¹ = (a * ℓ)⁻¹ := by group
        _ = (ℓ * a)⁻¹ := by rw [hc]
    rw [e]
    exact inv_mem haX

namespace Ctx

variable {t : G} (c : Ctx T M H S L t)
include c

theorem Y₂_le : c.data.Y₂ ≤ cj t L := fun _ hz => hz.1

theorem S_L₂_le_Y₂ : S ⊓ cj t L ≤ c.data.Y₂ := by
  rintro z ⟨hzS, hzL⟩
  exact ⟨hzL, 1, one_mem _, by
    rw [one_mul]
    exact ⟨c.data.S_le_M hzS, c.data.L₂_le_L₀ hzL⟩⟩

theorem O₂_le_S_L₂ : pCoreOf 2 (cj t L) ≤ S ⊓ cj t L := by
  have hS := c.isSylow_S_L₂
  exact pCoreOf_two_le_of_sylowIn hS.1 hS.2.1 hS.2.2

theorem N₂_normal {z n : G} (hz : z ∈ c.data.Y₂) (hn : n ∈ M ⊓ conjJoin S L ⊓ cj t L) :
    z * n * z⁻¹ ∈ M ⊓ conjJoin S L ⊓ cj t L := by
  obtain ⟨hzL, ℓ, hℓ, hX⟩ := hz
  have hnL : n ∈ cj t L := hn.2
  have hzn : z * n * z⁻¹ ∈ cj t L :=
    (cj t L).mul_mem ((cj t L).mul_mem hzL hnL) ((cj t L).inv_mem hzL)
  refine ⟨?_, hzn⟩
  have hc : ℓ * (z * n * z⁻¹) = (z * n * z⁻¹) * ℓ := c.data.comm_elem ℓ hℓ _ hzn
  have e : (ℓ * z) * n * (ℓ * z)⁻¹ = z * n * z⁻¹ :=
    calc (ℓ * z) * n * (ℓ * z)⁻¹ = ℓ * (z * n * z⁻¹) * ℓ⁻¹ := by group
      _ = (z * n * z⁻¹) * ℓ * ℓ⁻¹ := by rw [hc]
      _ = z * n * z⁻¹ := by group
  rw [← e]
  have hX' : ℓ * z ∈ M ⊓ conjJoin S L := hX
  exact (M ⊓ conjJoin S L).mul_mem ((M ⊓ conjJoin S L).mul_mem hX' hn.1)
    ((M ⊓ conjJoin S L).inv_mem hX')

omit [Finite G] c in
theorem cj_baumD {s : G} (hs : s ∈ S) : cj s (baumD S L) = baumD S L := by
  unfold baumD
  rw [cj_inf, cj_baum hs, cj_centralizer,
    mem_normalizer_iff_cj.1 (C56.S_le_normalizer_conjJoin L hs)]

variable {P₂ : A5Pi (cj t L)}

theorem L₂_le_Y₂_of_moves (hE : P₂.im (baum S) = Estd) {z : G} (hz : z ∈ c.data.Y₂)
    (hz4 : P₂.pf z 4 ≠ 4) : cj t L ≤ c.data.Y₂ := by
  have hV : Vstd ≤ P₂.im c.data.Y₂ := (c.im_V hE) ▸ P₂.im_mono c.S_L₂_le_Y₂
  have hYN : c.data.Y₂ ≤ Subgroup.normalizer (cj t L : Set G) :=
    c.Y₂_le.trans Subgroup.le_normalizer
  have hzN : z ∈ Subgroup.normalizer (cj t L : Set G) := hYN hz
  have hσ : P₂.pf z ∈ P₂.im c.data.Y₂ := pf_mem_im P₂.toPiData hYN hz
  have hev : Perm.sign (P₂.pf z) = 1 := by
    rw [P₂.pf_eq hzN, P₂.hπα z (c.Y₂_le hz)]
    exact Equiv.Perm.mem_alternatingGroup.1 (P₂.α ⟨z, c.Y₂_le hz⟩).2
  have hA := alt_le_of_V (P₂.im c.data.Y₂) hV hσ hz4 hev
  exact le_of_alt_le_im P₂ c.Y₂_le (c.O₂_le_S_L₂.trans c.S_L₂_le_Y₂) hA

theorem L₂_le_N₂ (hE : P₂.im (baum S) = Estd) (hY : cj t L ≤ c.data.Y₂) :
    cj t L ≤ M ⊓ conjJoin S L ⊓ cj t L := by
  have hSN : S ⊓ cj t L ≤ M ⊓ conjJoin S L ⊓ cj t L := fun z ⟨hzS, hzL⟩ =>
    ⟨⟨c.data.S_le_M hzS, c.data.L₂_le_L₀ hzL⟩, hzL⟩
  have hNL : M ⊓ conjJoin S L ⊓ cj t L ≤ cj t L := inf_le_right
  have hNN : M ⊓ conjJoin S L ⊓ cj t L ≤ Subgroup.normalizer (cj t L : Set G) :=
    hNL.trans Subgroup.le_normalizer
  have hV : Vstd ≤ P₂.im (M ⊓ conjJoin S L ⊓ cj t L) :=
    (c.im_V hE) ▸ P₂.im_mono hSN
  have hv : swap (0 : Fin 5) 1 * swap (2 : Fin 5) 3 ∈ P₂.im (M ⊓ conjJoin S L ⊓ cj t L) := hV vV_mem
  obtain ⟨v, hvN, hpv⟩ := (P₂.mem_im_pf hNN).1 hv
  have ha : a234 ∈ alternatingGroup (Fin 5) := Equiv.Perm.mem_alternatingGroup.2 a234_even
  obtain ⟨l, hl⟩ := P₂.hα ⟨a234, ha⟩
  have hlL : (l : G) ∈ cj t L := l.2
  have hpl : P₂.pf (l : G) = a234 := by
    rw [P₂.pf_eq (Subgroup.le_normalizer hlL), P₂.hπα (l : G) hlL]
    exact congrArg Subtype.val hl
  have hlv : (l : G) * v * (l : G)⁻¹ ∈ M ⊓ conjJoin S L ⊓ cj t L :=
    c.N₂_normal (hY hlL) hvN
  have hlvN : (l : G) * v * (l : G)⁻¹ ∈ Subgroup.normalizer (cj t L : Set G) := hNN hlv
  have hvN' : v ∈ Subgroup.normalizer (cj t L : Set G) := hNN hvN
  have hσ : swap (0 : Fin 5) 1 * swap (3 : Fin 5) 4 ∈ P₂.im (M ⊓ conjJoin S L ⊓ cj t L) := by
    refine (P₂.mem_im_pf hNN).2 ⟨(l : G) * v * (l : G)⁻¹, hlv, ?_⟩
    rw [P₂.toPiData.pf_mul (mul_mem (Subgroup.le_normalizer hlL) hvN') (inv_mem
      (Subgroup.le_normalizer hlL)), P₂.toPiData.pf_mul (Subgroup.le_normalizer hlL) hvN',
      P₂.toPiData.pf_inv (Subgroup.le_normalizer hlL), hpl, hpv]
    exact a234_conj
  have hA := alt_le_of_V _ hV hσ sigma_moves sigma_even
  exact le_of_alt_le_im P₂ hNL (c.O₂_le_S_L₂.trans hSN) hA

theorem fix4_Y₂ (hE : P₂.im (baum S) = Estd) : ∀ z ∈ c.data.Y₂, P₂.pf z 4 = 4 := by
  intro z hz
  by_contra hz4
  have hN := c.L₂_le_N₂ hE (c.L₂_le_Y₂_of_moves hE hz hz4)
  apply c.data.cs.not_le
  have hL₂M : cj t L ≤ M := fun x hx => (hN hx).1.1
  have h1 := cj_mono (t := t⁻¹) hL₂M
  rw [cj_cj, inv_mul_cancel, cj_one, c.data.cj_M (S.inv_mem c.data.t_mem)] at h1
  exact h1

theorem U₂_inf_D₀ : blockU (cj t L) ⊓ baumD S L = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx1, hx2⟩
  have : x ∈ baumD S L ⊓ (blockU L ⊔ blockU (cj t L)) := ⟨hx2, Subgroup.mem_sup_right hx1⟩
  rw [c.data.D₀_inf] at this
  exact this

theorem phi_comp {P₂ : A5Pi (cj t L)} (hI : P₂.im (s2I S L) = Estd) {f : G}
    (hf : f ∈ s2Phi S L) :
    ∃ u ∈ blockU (cj t L), ∃ d ∈ baumD S L, f = u * d ∧
      u ∈ Subgroup.centralizer (s2SI S L : Set G) := by
  obtain ⟨u, hu, d, hd, hfud⟩ := c.Phi_decomp hI hf.1
  refine ⟨u, hu, d, hd, hfud, Subgroup.mem_centralizer_iff.2 fun s hs => ?_⟩
  have hsS : s ∈ S := hs.1
  have hsN : s ∈ Subgroup.normalizer (cj t L : Set G) := c.SI_le_normalizer₂ hs
  have hsu : s * u * s⁻¹ ∈ blockU (cj t L) :=
    (Subgroup.mem_normalizer_iff.1 (C1.mem_normalizer_blockU hsN) u).1 hu
  have hsd : s * d * s⁻¹ ∈ baumD S L := by
    have := mul_mul_inv_mem_cj (t := s) hd
    rwa [cj_baumD hsS] at this
  have hsf : s * f = f * s := Subgroup.mem_centralizer_iff.1 hf.2 s hs
  have e : (s * u * s⁻¹) * (s * d * s⁻¹) = u * d := by
    have : s * f * s⁻¹ = f := by rw [hsf]; group
    rw [hfud] at this
    rw [← this]
    group
  have := (Lin2.unique_decomp c.U₂_inf_D₀ hsu hu hsd hd e).1
  calc s * u = (s * u * s⁻¹) * s := by group
    _ = u * s := by rw [this]

theorem X_le_cent (hE : P₂.im (baum S) = Estd) (hI : P₂.im (s2I S L) = Estd) :
    M ⊓ conjJoin S L ≤ Subgroup.centralizer (s2Phi S L : Set G) := by
  have h := c.data
  intro y hy
  have hyJ : y ∈ L ⊔ cj t L := h.join ▸ hy.2
  obtain ⟨ℓ, hℓ, z, hz, rfl⟩ := (Lin2.mem_sup_iff_of_le_normalizer h.L₂_le_normalizer).1 hyJ
  have hzY : z ∈ h.Y₂ := ⟨hz, ℓ, hℓ, hy⟩
  have hz4 := c.fix4_Y₂ hE z hzY
  refine Subgroup.mem_centralizer_iff.2 fun f hf => ?_
  obtain ⟨u, hu, d, hd, hfud, huC⟩ := c.phi_comp hI hf
  have hfI : f ∈ s2I S L := Subgroup.map_subtype_le _ hf.1
  have hzN : z ∈ Subgroup.normalizer (cj t L : Set G) := Subgroup.le_normalizer hz
  have hzu : z * u = u * z := by
    refine (P₂.comm_iff hzN hu).2 ?_
    rcases c.bf_cases hE hu huC with hb | hb
    · rw [hb]; exact vact_zero _
    · rw [hb]; exact vact_zv hz4
  have hzd : z * d = d * z := Subgroup.mem_centralizer_iff.1 hd.2 z (h.L₂_le_L₀ hz)
  have hℓf : ℓ * f = f * ℓ := Subgroup.mem_centralizer_iff.1 hfI.2 ℓ hℓ
  have hzf : z * f = f * z := by
    rw [hfud]
    calc z * (u * d) = (z * u) * d := by group
      _ = (u * z) * d := by rw [hzu]
      _ = u * (z * d) := by group
      _ = u * (d * z) := by rw [hzd]
      _ = (u * d) * z := by group
  calc f * (ℓ * z) = (f * ℓ) * z := by group
    _ = (ℓ * f) * z := by rw [hℓf]
    _ = ℓ * (f * z) := by group
    _ = ℓ * (z * f) := by rw [hzf]
    _ = (ℓ * z) * f := by group

theorem o3_cent (hE : P₂.im (baum S) = Estd) (hI : P₂.im (s2I S L) = Estd) :
    pElementsGen 3 (M ⊓ conjJoin S L) ≤ Subgroup.centralizer (s2Phi S L : Set G) :=
  (Subgroup.closure_le _).2 fun _ hx => c.X_le_cent hE hI hx.1

end Ctx

end CFSG.QuasithinUnique.A5.S2
