module

public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin
open CFSG.Quasithin.B6
open scoped commutatorElement Pointwise

variable {Ω : Type*}

local notation3 "conjSup(" G ", " L ")" => (⨆ g ∈ G, conjSub g L)
local notation3 "otherConjSup(" G ", " L ")" =>
  (⨆ g ∈ G, ⨆ (_ : conjSub g L ≠ L), conjSub g L)
local notation3 "conjIntersection(" S ", " B ", " C ")" =>
  (⨅ s ∈ S, (conjSub s B ⊔ conjSub s C))

section Transport

variable [Group Ω]

private lemma isUniqueMaxOver_conjSub_iff {H T M : Subgroup Ω} {g : Ω} :
    IsUniqueMaxOver (conjSub g H) (conjSub g T) (conjSub g M) ↔
      IsUniqueMaxOver H T M := by
  unfold IsUniqueMaxOver
  rw [maxOver_conjSub, ← Set.image_singleton,
    (Set.image_injective.mpr (conjSub g).injective).eq_iff]

private lemma conjSub_normalizer (g : Ω) (K : Subgroup Ω) :
    conjSub g (Subgroup.normalizer (K : Set Ω)) =
      Subgroup.normalizer (conjSub g K : Set Ω) := by
  simpa [conjSub, MulEquiv.coe_mapSubgroup] using
    Subgroup.map_equiv_normalizer_eq K (MulAut.conj g)

private lemma conjSub_iSup {ι : Sort*} (g : Ω) (s : ι → Subgroup Ω) :
    conjSub g (⨆ i, s i) = ⨆ i, conjSub g (s i) := by
  simp [conjSub]

private lemma conjSub_inf (g : Ω) (H K : Subgroup Ω) :
    conjSub g (H ⊓ K) = conjSub g H ⊓ conjSub g K := by
  simp [conjSub]

private lemma conjSub_sup (g : Ω) (H K : Subgroup Ω) :
    conjSub g (H ⊔ K) = conjSub g H ⊔ conjSub g K := by
  simp [conjSub]

private lemma conjSub_commutator (g : Ω) (H K : Subgroup Ω) :
    conjSub g ⁅H, K⁆ = ⁅conjSub g H, conjSub g K⁆ := by
  simpa [conjSub, MulEquiv.coe_mapSubgroup] using
    Subgroup.map_commutator H K (MulAut.conj g).toMonoidHom

private lemma commutator_conj_eq_bot_of_ne {G L : Subgroup Ω}
    (hcomm : ∀ g ∈ G, conjSub g L ≠ L → ⁅L, conjSub g L⁆ = ⊥)
    {a b : Ω} (ha : a ∈ G) (hb : b ∈ G) (hne : conjSub a L ≠ conjSub b L) :
    ⁅conjSub a L, conjSub b L⁆ = ⊥ := by
  have hne' : conjSub (b⁻¹ * a) L ≠ L := by
    intro h
    apply hne
    have := congrArg (conjSub b) h
    rwa [← conjSub_mul, show b * (b⁻¹ * a) = a by group] at this
  have hb' : ⁅L, conjSub (b⁻¹ * a) L⁆ = ⊥ :=
    hcomm (b⁻¹ * a) (G.mul_mem (G.inv_mem hb) ha) hne'
  have hmap : ⁅conjSub b L, conjSub a L⁆ = ⊥ := by
    have h := congrArg (conjSub b) hb'
    rw [conjSub_commutator] at h
    rw [show conjSub b (conjSub (b⁻¹ * a) L) = conjSub a L by
      rw [← conjSub_mul, show b * (b⁻¹ * a) = a by group]] at h
    simpa using h
  rw [Subgroup.commutator_comm]
  exact hmap

end Transport

section Product

variable [Group Ω]

private lemma le_conjSup (G L : Subgroup Ω) : L ≤ conjSup(G, L) := by
  exact le_iSup₂_of_le (1 : Ω) G.one_mem (le_of_eq (conjSub_one L).symm)

private lemma otherConjSup_le_conjSup (G L : Subgroup Ω) :
    otherConjSup(G, L) ≤ conjSup(G, L) := by
  refine iSup_le fun g => iSup_le fun hg => iSup_le fun hne => ?_
  exact le_iSup₂_of_le g hg le_rfl

private lemma conjSup_le {G L : Subgroup Ω} (hLG : L ≤ G) : conjSup(G, L) ≤ G := by
  refine iSup_le fun g => iSup_le fun hg => ?_
  change L.map (MulAut.conj g).toMonoidHom ≤ G
  rw [Subgroup.map_le_iff_le_comap]
  intro x hx
  simpa [MulAut.conj_apply] using G.mul_mem (G.mul_mem hg (hLG hx)) (G.inv_mem hg)

private lemma conjSup_eq_sup (G L : Subgroup Ω) :
    conjSup(G, L) = L ⊔ otherConjSup(G, L) := by
  apply le_antisymm
  · refine iSup_le fun g => iSup_le fun hg => ?_
    by_cases hne : conjSub g L = L
    · rw [hne]; exact le_sup_left
    · have hinner : conjSub g L ≤ (⨆ (_ : conjSub g L ≠ L), conjSub g L) :=
        le_iSup (fun _ : conjSub g L ≠ L => conjSub g L) hne
      have hleC : conjSub g L ≤ otherConjSup(G, L) :=
        le_iSup₂_of_le g hg hinner
      exact hleC.trans le_sup_right
  · exact sup_le (le_conjSup G L) (otherConjSup_le_conjSup G L)

private lemma otherConjSup_le_centralizer {G L : Subgroup Ω}
    (hcomm : ∀ g ∈ G, conjSub g L ≠ L → ⁅L, conjSub g L⁆ = ⊥) :
    otherConjSup(G, L) ≤ Subgroup.centralizer (L : Set Ω) := by
  refine iSup_le fun g => iSup_le fun hg => iSup_le fun hne => ?_
  exact Subgroup.le_centralizer_iff.mp
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcomm g hg hne))

private lemma conjSup_normal {G L : Subgroup Ω} {g : Ω} (hg : g ∈ G) :
    conjSub g (conjSup(G, L)) = conjSup(G, L) := by
  apply le_antisymm
  · rw [conjSub_iSup]
    refine iSup_le fun h => ?_
    rw [conjSub_iSup]
    refine iSup_le fun hh => ?_
    rw [← conjSub_mul]
    exact le_iSup₂_of_le (g * h) (G.mul_mem hg hh) le_rfl
  · have h1 : conjSub g⁻¹ (conjSup(G, L)) ≤ conjSup(G, L) := by
      rw [conjSub_iSup]
      refine iSup_le fun h => ?_
      rw [conjSub_iSup]
      refine iSup_le fun hh => ?_
      rw [← conjSub_mul]
      exact le_iSup₂_of_le (g⁻¹ * h) (G.mul_mem (G.inv_mem hg) hh) le_rfl
    have h2 := (conjSub g).monotone h1
    rwa [← conjSub_mul, mul_inv_cancel, conjSub_one] at h2

private lemma conjSup_conjSub {G L : Subgroup Ω} {s : Ω} (hs : s ∈ G) :
    conjSup(G, conjSub s L) = conjSup(G, L) := by
  apply le_antisymm
  · refine iSup_le fun g => iSup_le fun hg => ?_
    rw [← conjSub_mul]
    exact le_iSup₂_of_le (g * s) (G.mul_mem hg hs) le_rfl
  · refine iSup_le fun u => iSup_le fun hu => ?_
    refine le_iSup₂_of_le (u * s⁻¹) (G.mul_mem hu (G.inv_mem hs)) ?_
    exact le_of_eq (show conjSub u L = conjSub (u * s⁻¹) (conjSub s L) by
      rw [← conjSub_mul, show (u * s⁻¹) * s = u by group])

private lemma conjSup_le_normalizer_conj {G L : Subgroup Ω}
    (hcomm : ∀ g ∈ G, conjSub g L ≠ L → ⁅L, conjSub g L⁆ = ⊥) {u : Ω} (hu : u ∈ G) :
    conjSup(G, L) ≤ Subgroup.normalizer (conjSub u L : Set Ω) := by
  refine iSup_le fun g => iSup_le fun hg => ?_
  by_cases hgu : conjSub g L = conjSub u L
  · rw [hgu]; exact Subgroup.le_normalizer
  · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (commutator_conj_eq_bot_of_ne (G := G) (L := L) hcomm hg hu hgu)).trans
      (Subgroup.centralizer_le_normalizer _)

private lemma conjIntersection_le (S B C : Subgroup Ω) :
    conjIntersection(S, B, C) ≤ B ⊔ C := by
  have h := (iInf_le (fun s => ⨅ (_ : s ∈ S), (conjSub s B ⊔ conjSub s C)) 1).trans
    (iInf_le (fun _ : (1 : Ω) ∈ S => conjSub 1 B ⊔ conjSub 1 C) S.one_mem)
  simpa [conjSub_one] using h

private lemma le_normalizer_conjIntersection (S B C : Subgroup Ω) :
    S ≤ Subgroup.normalizer ((conjIntersection(S, B, C) : Subgroup Ω) : Set Ω) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro d
  constructor
  · intro hd
    simp only [Subgroup.mem_iInf] at hd ⊢
    intro t ht
    have hd' : d ∈ conjSub (s⁻¹ * t) (B ⊔ C) := by
      rw [conjSub_sup]
      exact hd (s⁻¹ * t) (S.mul_mem (S.inv_mem hs) ht)
    rw [mem_conjSub] at hd'
    rw [← conjSub_sup, mem_conjSub]
    simpa [MulAut.conj_apply, mul_assoc] using hd'
  · intro hd
    simp only [Subgroup.mem_iInf] at hd ⊢
    intro t ht
    have hd' : s * d * s⁻¹ ∈ conjSub (s * t) (B ⊔ C) := by
      rw [conjSub_sup]
      exact hd (s * t) (S.mul_mem hs ht)
    rw [mem_conjSub] at hd'
    rw [← conjSub_sup, mem_conjSub]
    simpa [mul_assoc] using hd'


private lemma coe_mul_of_eq_sup {L N C : Subgroup Ω} (hNLC : N = L ⊔ C)
    (hLC : C ≤ Subgroup.centralizer (L : Set Ω)) :
    (N : Set Ω) = (↑L : Set Ω) * (↑C : Set Ω) := by
  rw [hNLC]
  exact Subgroup.coe_mul_of_right_le_normalizer_left L C
    (hLC.trans (Subgroup.centralizer_le_normalizer (L : Set Ω)))

private lemma coe_mul_inf_sup {L N C H : Subgroup Ω} (hNLC : N = L ⊔ C)
    (hLC : C ≤ Subgroup.centralizer (L : Set Ω)) :
    (↑(H ⊓ N ⊔ C) : Set Ω) = (↑(H ⊓ N) : Set Ω) * (↑C : Set Ω) := by
  have hNC : N ≤ Subgroup.normalizer (C : Set Ω) := by
    rw [hNLC]
    exact sup_le ((Subgroup.le_centralizer_iff.mp hLC).trans
      (Subgroup.centralizer_le_normalizer (C : Set Ω))) Subgroup.le_normalizer
  exact Subgroup.coe_mul_of_left_le_normalizer_right (H ⊓ N) C
    ((inf_le_right : H ⊓ N ≤ N).trans hNC)

private lemma coe_mul_sup_normalizer {G N S : Subgroup Ω} (hG : N ⊔ S = G)
    (hSN : S ≤ Subgroup.normalizer (N : Set Ω)) :
    (G : Set Ω) = (↑N : Set Ω) * (↑S : Set Ω) := by
  rw [← hG]
  exact Subgroup.coe_mul_of_right_le_normalizer_left N S hSN

private lemma le_normalizer_inf_of_le {N X L : Subgroup Ω}
    (hXN : X ≤ N) (hNL : N ≤ Subgroup.normalizer (L : Set Ω)) :
    X ≤ Subgroup.normalizer ((X ⊓ L : Subgroup Ω) : Set Ω) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact Subgroup.mem_inf.mpr
      ⟨X.mul_mem (X.mul_mem hx hy.1) (X.inv_mem hx),
       (Subgroup.mem_normalizer_iff.mp (hNL (hXN hx)) y).mp hy.2⟩
  · intro hy
    have hyX : y ∈ X := by
      have h := X.mul_mem (X.mul_mem (X.inv_mem hx) hy.1) hx
      simpa [mul_assoc] using h
    have hxinv : x⁻¹ ∈ Subgroup.normalizer (L : Set Ω) :=
      (Subgroup.normalizer (L : Set Ω)).inv_mem (hNL (hXN hx))
    have hyL : y ∈ L := by
      have h := (Subgroup.mem_normalizer_iff.mp hxinv (x * y * x⁻¹)).mp hy.2
      simpa [mul_assoc] using h
    exact Subgroup.mem_inf.mpr ⟨hyX, hyL⟩

private lemma conjSub_le_centralizer_conjSub {L C : Subgroup Ω} (s : Ω)
    (hC : C ≤ Subgroup.centralizer (L : Set Ω)) :
    conjSub s C ≤ Subgroup.centralizer (conjSub s L : Set Ω) := by
  intro c' hc'
  rw [Subgroup.mem_centralizer_iff]
  intro l' hl'
  obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hc'
  obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hl'
  have hcl : l * c = c * l := Subgroup.mem_centralizer_iff.mp (hC hc) l hl
  rw [← map_mul, ← map_mul, hcl]

private lemma conjSup_eq_conjSub_sup {G L : Subgroup Ω} {s : Ω} (hs : s ∈ G) :
    conjSup(G, L) = conjSub s L ⊔ conjSub s (otherConjSup(G, L)) := by
  calc conjSup(G, L) = conjSub s (conjSup(G, L)) :=
        (conjSup_normal (G := G) (L := L) hs).symm
    _ = conjSub s (L ⊔ otherConjSup(G, L)) := by rw [conjSup_eq_sup]
    _ = conjSub s L ⊔ conjSub s (otherConjSup(G, L)) := conjSub_sup s L _

private lemma normalizer_conjSub_transport {L S : Subgroup Ω}
    (hnormal : ∀ K : Subgroup Ω, S ⊓ L ≤ K → K ≤ L →
      L ≤ Subgroup.normalizer (K : Set Ω) → K = L)
    {s : Ω} (hs : s ∈ S) :
    ∀ K : Subgroup Ω, S ⊓ conjSub s L ≤ K → K ≤ conjSub s L →
      conjSub s L ≤ Subgroup.normalizer (K : Set Ω) → K = conjSub s L := by
  intro K hSK hKL hNK
  have hK' : conjSub s⁻¹ K = L := by
    refine hnormal (conjSub s⁻¹ K) ?_ ?_ ?_
    · intro z hz
      rw [mem_conjSub]
      have hszS : s * z * s⁻¹ ∈ S := by
        simpa [MulAut.conj_apply] using S.mul_mem (S.mul_mem hs hz.1) (S.inv_mem hs)
      have hszL : s * z * s⁻¹ ∈ conjSub s L := by
        rw [mem_conjSub]
        have hz_eq : s⁻¹ * (s * z * s⁻¹) * s = z := by group
        rw [hz_eq]
        exact hz.2
      simpa using hSK ⟨hszS, hszL⟩
    · have h := (conjSub s⁻¹).monotone hKL
      rwa [← conjSub_mul, inv_mul_cancel, conjSub_one] at h
    · have h := (conjSub s⁻¹).monotone hNK
      rw [← conjSub_mul, inv_mul_cancel, conjSub_one] at h
      rwa [conjSub_normalizer] at h
  have := congrArg (conjSub s) hK'
  rwa [← conjSub_mul, mul_inv_cancel, conjSub_one] at this

private lemma conjSup_le_normalizer_conjSub {G L S : Subgroup Ω}
    (hSG : S ≤ G)
    (hcomm : ∀ g ∈ G, conjSub g L ≠ L → ⁅L, conjSub g L⁆ = ⊥)
    {s t : Ω} (hs : s ∈ S) (ht : t ∈ S) :
    conjSup(G, L) ≤ Subgroup.normalizer (conjSub t (conjSub s L) : Set Ω) := by
  have h := conjSup_le_normalizer_conj (G := G) (L := L) hcomm
    (G.mul_mem (hSG ht) (hSG hs))
  rwa [conjSub_mul] at h

end Product

section MainClaim

variable [Group Ω] [Finite Ω]

omit [Finite Ω] in
private lemma le_inf_of_inf_sup_eq {S L N C H : Subgroup Ω}
    (hNLC : N = L ⊔ C)
    (hLC : C ≤ Subgroup.centralizer (L : Set Ω))
    (hNL : N ≤ Subgroup.normalizer (L : Set Ω))
    (hnormal : ∀ K : Subgroup Ω, S ⊓ L ≤ K → K ≤ L →
      L ≤ Subgroup.normalizer (K : Set Ω) → K = L)
    (hSH : S ≤ H)
    (hPL : (H ⊓ N ⊔ C) ⊓ L = L) :
    L ≤ H ⊓ N := by
  have hLleN : L ≤ N := by rw [hNLC]; exact le_sup_left
  have hXCset := coe_mul_inf_sup (H := H) hNLC hLC
  have hLle : L ≤ H ⊓ N ⊔ C := by
    rw [← hPL]
    exact inf_le_left
  let K : Subgroup Ω := (H ⊓ N) ⊓ L
  have hSK : S ⊓ L ≤ K := by
    change S ⊓ L ≤ (H ⊓ N) ⊓ L
    exact le_inf (le_inf (le_trans inf_le_left hSH) (inf_le_right.trans hLleN)) inf_le_right
  have hKL : K ≤ L := by
    change (H ⊓ N) ⊓ L ≤ L
    exact inf_le_right
  have hLK : L ≤ Subgroup.normalizer (K : Set Ω) := by
    intro l hl
    obtain ⟨x, hxX, c, hcC, hxc⟩ : ∃ x ∈ H ⊓ N, ∃ c ∈ C, x * c = l := by
      have hl' : l ∈ (↑(H ⊓ N) : Set Ω) * (↑C : Set Ω) := by
        rw [← hXCset]
        exact hLle hl
      exact Set.mem_mul.mp hl'
    have hxK : x ∈ Subgroup.normalizer (K : Set Ω) :=
      le_normalizer_inf_of_le (X := H ⊓ N) (N := N) (L := L) inf_le_right hNL hxX
    have hcK : c ∈ Subgroup.normalizer (K : Set Ω) :=
      Subgroup.centralizer_le_normalizer (K : Set Ω)
        (Subgroup.mem_centralizer_iff.mpr fun y hy =>
          Subgroup.mem_centralizer_iff.mp (hLC hcC) y (Subgroup.mem_inf.mp hy).2)
    rw [← hxc]
    exact (Subgroup.normalizer (K : Set Ω)).mul_mem hxK hcK
  have hLleK : L ≤ K := by rw [hnormal K hSK hKL hLK]
  intro l hl
  exact (Subgroup.mem_inf.mp (hLleK hl)).1

omit [Finite Ω] in
private lemma le_of_le_inf {G S L N H : Subgroup Ω}
    (hG : N ⊔ S = G)
    (hSN : S ≤ Subgroup.normalizer (N : Set Ω))
    (hNsup : N ≤ conjSup(G, L))
    (hNconj : ∀ t ∈ S, N ≤ Subgroup.normalizer (conjSub t L : Set Ω))
    (hSH : S ≤ H) (hLH : L ≤ H) :
    G ≤ H := by
  have hNleH : N ≤ H := by
    refine hNsup.trans ?_
    refine iSup_le fun g => iSup_le fun hg => ?_
    have hgNS : g ∈ (↑N : Set Ω) * (↑S : Set Ω) := by
      rw [← coe_mul_sup_normalizer hG hSN]
      exact hg
    obtain ⟨n, hnN, s, hsS, hns⟩ := Set.mem_mul.mp hgNS
    have hfix : conjSub n (conjSub s L) = conjSub s L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hNconj s hsS hnN)
    have hg' : conjSub g L = conjSub s L := by
      rw [← hns, conjSub_mul, hfix]
    rw [hg']
    intro y hy
    rw [mem_conjSub] at hy
    have : y = s * (s⁻¹ * y * s) * s⁻¹ := by group
    rw [this]
    exact H.mul_mem (H.mul_mem (hSH hsS) (hLH hy)) (H.inv_mem (hSH hsS))
  rw [← hG]
  exact sup_le hNleH hSH

omit [Finite Ω] in
private lemma le_of_sup_inf_eq {G S L N C H : Subgroup Ω}
    (hG : N ⊔ S = G)
    (hSN : S ≤ Subgroup.normalizer (N : Set Ω))
    (hNsup : N ≤ conjSup(G, L))
    (hNconj : ∀ t ∈ S, N ≤ Subgroup.normalizer (conjSub t L : Set Ω))
    (hnormal : ∀ K : Subgroup Ω, S ⊓ L ≤ K → K ≤ L →
      L ≤ Subgroup.normalizer (K : Set Ω) → K = L)
    (hLC : C ≤ Subgroup.centralizer (L : Set Ω))
    (hNLC : N = L ⊔ C)
    (hSH : S ≤ H)
    (hPL : (H ⊓ N ⊔ C) ⊓ L = L) :
    G ≤ H := by
  have hNL : N ≤ Subgroup.normalizer (L : Set Ω) := by
    simpa [conjSub_one] using hNconj 1 S.one_mem
  have hLleX : L ≤ H ⊓ N := le_inf_of_inf_sup_eq hNLC hLC hNL hnormal hSH hPL
  exact le_of_le_inf hG hSN hNsup hNconj hSH (hLleX.trans inf_le_left)

private theorem main_claim_ne {S L B N C H : Subgroup Ω}
    (hNLC : N = L ⊔ C)
    (hLC : C ≤ Subgroup.centralizer (L : Set Ω))
    (hB : IsUniqueMaxOver L (S ⊓ L) B)
    (hSH : S ≤ H)
    (hPL : (H ⊓ N ⊔ C) ⊓ L ≠ L) :
    H ⊓ N ≤ B ⊔ C := by
  have hLleN : L ≤ N := by rw [hNLC]; exact le_sup_left
  have hNset := coe_mul_of_eq_sup hNLC hLC
  have hPLt : (H ⊓ N ⊔ C) ⊓ L < L := lt_of_le_of_ne inf_le_right hPL
  have hSP : S ⊓ L ≤ (H ⊓ N ⊔ C) ⊓ L := by
    refine le_inf ?_ inf_le_right
    have hSX : S ⊓ L ≤ H ⊓ N :=
      le_inf (le_trans inf_le_left hSH) (inf_le_right.trans hLleN)
    exact hSX.trans le_sup_left
  obtain ⟨M₀, hM₀, hPM₀⟩ := exists_isMaxSubgroupIn hPLt
  have hM₀B : M₀ = B := (isUniqueMaxOver_iff.mp hB).2.2 M₀ hM₀ (hSP.trans hPM₀)
  intro z hz
  obtain ⟨y, hyL, c, hcC, hyc⟩ : ∃ y ∈ L, ∃ c ∈ C, y * c = z := by
    have hz' : z ∈ (↑L : Set Ω) * (↑C : Set Ω) := by
      rw [← hNset]
      exact hz.2
    exact Set.mem_mul.mp hz'
  have hyP : y ∈ (H ⊓ N ⊔ C) ⊓ L := by
    refine ⟨?_, hyL⟩
    have h : z * c⁻¹ ∈ (H ⊓ N) ⊔ C :=
      Subgroup.mul_mem_sup hz (C.inv_mem hcC)
    rwa [show z * c⁻¹ = y by rw [← hyc]; group] at h
  have h := Subgroup.mul_mem_sup (hM₀B ▸ hPM₀ hyP) hcC
  rwa [hyc] at h

private theorem main_claim {G S L B N C H : Subgroup Ω}
    (hG : N ⊔ S = G)
    (hSN : S ≤ Subgroup.normalizer (N : Set Ω))
    (hNsup : N ≤ conjSup(G, L))
    (hB : IsUniqueMaxOver L (S ⊓ L) B)
    (hnormal : ∀ K : Subgroup Ω, S ⊓ L ≤ K → K ≤ L →
      L ≤ Subgroup.normalizer (K : Set Ω) → K = L)
    (hLC : C ≤ Subgroup.centralizer (L : Set Ω))
    (hNLC : N = L ⊔ C)
    (hNconj : ∀ t ∈ S, N ≤ Subgroup.normalizer (conjSub t L : Set Ω))
    (hSH : S ≤ H) (hHG : H < G) :
    H ⊓ N ≤ B ⊔ C := by
  by_cases hPL : (H ⊓ N ⊔ C) ⊓ L = L
  · exfalso
    exact (ne_of_lt hHG) (le_antisymm hHG.le
      (le_of_sup_inf_eq hG hSN hNsup hNconj hnormal hLC hNLC hSH hPL))
  · exact main_claim_ne hNLC hLC hB hSH hPL

end MainClaim

section Existence

variable [Group Ω] [Finite Ω]

omit [Finite Ω] in
private lemma commute_conjSub_form {G L : Subgroup Ω}
    (hcomm : ∀ g ∈ G, L.map (MulAut.conj g).toMonoidHom ≠ L →
      ⁅L, L.map (MulAut.conj g).toMonoidHom⁆ = ⊥) :
    ∀ g ∈ G, conjSub g L ≠ L → ⁅L, conjSub g L⁆ = ⊥ := by
  intro g hg hne
  have hne' : L.map (MulAut.conj g).toMonoidHom ≠ L := by
    simpa [conjSub, MulEquiv.coe_mapSubgroup] using hne
  have := hcomm g hg hne'
  simpa [conjSub, MulEquiv.coe_mapSubgroup] using this

omit [Finite Ω] in
private lemma conjSup_sup_eq {G L S : Subgroup Ω}
    (hG : (⨆ g ∈ G, L.map (MulAut.conj g).toMonoidHom) ⊔ S = G) :
    conjSup(G, L) ⊔ S = G := by
  simpa [conjSub, MulEquiv.coe_mapSubgroup] using hG

omit [Finite Ω] in
private lemma le_normalizer_conjSup {G L S : Subgroup Ω} (hSG : S ≤ G) :
    S ≤ Subgroup.normalizer ((conjSup(G, L) : Subgroup Ω) : Set Ω) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact conjSup_normal (G := G) (L := L) (hSG hs)

omit [Finite Ω] in
private lemma lt_of_isUniqueMaxOver_inf {G L S B : Subgroup Ω} (hLG : L ≤ G) (hSG : S ≤ G)
    (hB : IsUniqueMaxOver L (S ⊓ L) B) : S < G := by
  refine lt_of_le_of_ne hSG ?_
  intro hSGeq
  have hmaxB : IsMaxSubgroupIn L B := (isUniqueMaxOver_iff.mp hB).1
  have hSL : S ⊓ L = L := inf_eq_right.mpr (by rw [hSGeq]; exact hLG)
  have hLB : L ≤ B := by
    have := (isUniqueMaxOver_iff.mp hB).2.1
    rwa [hSL] at this
  exact (ne_of_lt hmaxB.1) (le_antisymm hmaxB.le hLB)

private lemma le_conjIntersection {G L S B : Subgroup Ω}
    (hSG : S ≤ G) (hG' : conjSup(G, L) ⊔ S = G)
    (hSN : S ≤ Subgroup.normalizer ((conjSup(G, L) : Subgroup Ω) : Set Ω))
    (hcomm : ∀ g ∈ G, conjSub g L ≠ L → ⁅L, conjSub g L⁆ = ⊥)
    (hB : IsUniqueMaxOver L (S ⊓ L) B)
    (hnormal : ∀ K : Subgroup Ω, S ⊓ L ≤ K → K ≤ L →
      L ≤ Subgroup.normalizer (K : Set Ω) → K = L)
    {H : Subgroup Ω} (hSH : S ≤ H) (hHG : H < G) :
    H ⊓ conjSup(G, L) ≤ conjIntersection(S, B, otherConjSup(G, L)) := by
  refine le_iInf fun s => le_iInf fun hs => ?_
  have hB_s : IsUniqueMaxOver (conjSub s L) (S ⊓ conjSub s L) (conjSub s B) := by
    have h := (isUniqueMaxOver_conjSub_iff (g := s)).mpr hB
    rwa [conjSub_inf, conjSub_eq_self (Subgroup.le_normalizer hs)] at h
  have hLC_s := conjSub_le_centralizer_conjSub s
    (otherConjSup_le_centralizer (G := G) (L := L) hcomm)
  have hNLC_s := conjSup_eq_conjSub_sup (G := G) (L := L) (hSG hs)
  have hnormal_s := normalizer_conjSub_transport hnormal hs
  have hNconj_s : ∀ t ∈ S, conjSup(G, L) ≤
      Subgroup.normalizer (conjSub t (conjSub s L) : Set Ω) :=
    fun t ht => conjSup_le_normalizer_conjSub hSG hcomm hs ht
  have hNsup_s : conjSup(G, L) ≤ conjSup(G, conjSub s L) := by
    rw [conjSup_conjSub (G := G) (L := L) (hSG hs)]
  exact main_claim hG' hSN hNsup_s hB_s hnormal_s hLC_s hNLC_s hNconj_s hSH hHG

omit [Finite Ω] in
private lemma le_sup_of_le_conjIntersection {G L S B : Subgroup Ω}
    (hG' : conjSup(G, L) ⊔ S = G)
    (hSN : S ≤ Subgroup.normalizer ((conjSup(G, L) : Subgroup Ω) : Set Ω))
    {H : Subgroup Ω} (hSH : S ≤ H) (hHG : H < G)
    (hHN : H ⊓ conjSup(G, L) ≤ conjIntersection(S, B, otherConjSup(G, L))) :
    H ≤ conjIntersection(S, B, otherConjSup(G, L)) ⊔ S := by
  intro h hhH
  have hhG : h ∈ G := hHG.le hhH
  have hhNS : h ∈ (↑(conjSup(G, L)) : Set Ω) * (↑S : Set Ω) := by
    rw [← coe_mul_sup_normalizer hG' hSN]
    exact hhG
  obtain ⟨n, hnN, t, htS, hnt⟩ := Set.mem_mul.mp hhNS
  have hnH : n ∈ H := by
    have hmem : h * t⁻¹ ∈ H := H.mul_mem hhH (H.inv_mem (hSH htS))
    have ht_eq : h * t⁻¹ = n := by rw [← hnt]; group
    rwa [ht_eq] at hmem
  have hnD : n ∈ conjIntersection(S, B, otherConjSup(G, L)) := hHN ⟨hnH, hnN⟩
  have hmem : n * t ∈ conjIntersection(S, B, otherConjSup(G, L)) ⊔ S :=
    Subgroup.mul_mem_sup hnD htS
  rwa [hnt] at hmem

private lemma conjSup_le_sup_of_sup_eq {G L S B : Subgroup Ω}
    (hLG : L ≤ G) (hSG : S ≤ G)
    (hG' : conjSup(G, L) ⊔ S = G)
    (hSN : S ≤ Subgroup.normalizer ((conjSup(G, L) : Subgroup Ω) : Set Ω))
    (hcomm : ∀ g ∈ G, conjSub g L ≠ L → ⁅L, conjSub g L⁆ = ⊥)
    (hB : IsUniqueMaxOver L (S ⊓ L) B)
    (hnormal : ∀ K : Subgroup Ω, S ⊓ L ≤ K → K ≤ L →
      L ≤ Subgroup.normalizer (K : Set Ω) → K = L)
    (hSltG : S < G)
    (hDleBC : conjIntersection(S, B, otherConjSup(G, L)) ≤ B ⊔ otherConjSup(G, L))
    (hDset : (↑(conjIntersection(S, B, otherConjSup(G, L)) ⊔ S) : Set Ω) =
      ((conjIntersection(S, B, otherConjSup(G, L)) : Subgroup Ω) : Set Ω) * (↑S : Set Ω))
    (hMG : conjIntersection(S, B, otherConjSup(G, L)) ⊔ S = G) :
    conjSup(G, L) ≤ B ⊔ otherConjSup(G, L) := by
  have hmaxB : IsMaxSubgroupIn L B := (isUniqueMaxOver_iff.mp hB).1
  have hDleN : conjIntersection(S, B, otherConjSup(G, L)) ≤ conjSup(G, L) :=
    hDleBC.trans (sup_le (hmaxB.le.trans (le_conjSup G L)) (otherConjSup_le_conjSup G L))
  have hNle : conjSup(G, L) ≤ conjIntersection(S, B, otherConjSup(G, L)) ⊔
      (S ⊓ conjSup(G, L)) := by
    intro n hn
    have hnDS : n ∈ ((conjIntersection(S, B, otherConjSup(G, L)) : Subgroup Ω) : Set Ω) *
        (↑S : Set Ω) := by
      rw [← hDset, hMG]
      exact conjSup_le hLG hn
    obtain ⟨d, hdD, t, htS, hdt⟩ := Set.mem_mul.mp hnDS
    have htN : t ∈ conjSup(G, L) := by
      have hmem : d⁻¹ * n ∈ conjSup(G, L) :=
        (conjSup(G, L)).mul_mem ((conjSup(G, L)).inv_mem (hDleN hdD)) hn
      have ht_eq : d⁻¹ * n = t := by rw [← hdt]; group
      rwa [ht_eq] at hmem
    have h := Subgroup.mul_mem_sup hdD (Subgroup.mem_inf.mpr ⟨htS, htN⟩)
    rwa [hdt] at h
  have hmainS : S ⊓ conjSup(G, L) ≤ B ⊔ otherConjSup(G, L) :=
    main_claim hG' hSN le_rfl hB hnormal
      (otherConjSup_le_centralizer (G := G) (L := L) hcomm)
      (conjSup_eq_sup G L)
      (fun t ht => conjSup_le_normalizer_conj (G := G) (L := L) hcomm (hSG ht))
      le_rfl hSltG
  exact hNle.trans (sup_le hDleBC hmainS)

omit [Finite Ω] in
private lemma not_conjSup_le_sup {G L S B : Subgroup Ω}
    (hcomm : ∀ g ∈ G, conjSub g L ≠ L → ⁅L, conjSub g L⁆ = ⊥)
    (hB : IsUniqueMaxOver L (S ⊓ L) B)
    (hnormal : ∀ K : Subgroup Ω, S ⊓ L ≤ K → K ≤ L →
      L ≤ Subgroup.normalizer (K : Set Ω) → K = L)
    (h : conjSup(G, L) ≤ B ⊔ otherConjSup(G, L)) : False := by
  have hmaxB : IsMaxSubgroupIn L B := (isUniqueMaxOver_iff.mp hB).1
  have hLleBC : L ≤ B ⊔ otherConjSup(G, L) := (le_conjSup G L).trans h
  have hCB : otherConjSup(G, L) ≤ Subgroup.centralizer (B : Set Ω) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact Subgroup.mem_centralizer_iff.mp
      (otherConjSup_le_centralizer (G := G) (L := L) hcomm hc) b (hmaxB.le hb)
  have hBCset : (↑(B ⊔ otherConjSup(G, L)) : Set Ω) =
      (↑B : Set Ω) * (↑(otherConjSup(G, L)) : Set Ω) :=
    Subgroup.coe_mul_of_right_le_normalizer_left B (otherConjSup(G, L))
      (hCB.trans (Subgroup.centralizer_le_normalizer (B : Set Ω)))
  have hLdecomp : L ≤ B ⊔ (L ⊓ otherConjSup(G, L)) := by
    intro l hl
    have hl' : l ∈ (↑B : Set Ω) * (↑(otherConjSup(G, L)) : Set Ω) := by
      rw [← hBCset]
      exact hLleBC hl
    obtain ⟨b, hbB, c, hcC, hbc⟩ := Set.mem_mul.mp hl'
    have hcL : c ∈ L := by
      have hmem : b⁻¹ * l ∈ L := L.mul_mem (L.inv_mem (hmaxB.le hbB)) hl
      have hc_eq : b⁻¹ * l = c := by rw [← hbc]; group
      rwa [hc_eq] at hmem
    have h := Subgroup.mul_mem_sup hbB (Subgroup.mem_inf.mpr ⟨hcL, hcC⟩)
    rwa [hbc] at h
  have hLeq : L = B ⊔ (L ⊓ otherConjSup(G, L)) :=
    le_antisymm hLdecomp (sup_le hmaxB.le inf_le_left)
  have hLnormB : L ≤ Subgroup.normalizer (B : Set Ω) := by
    rw [hLeq]
    exact sup_le Subgroup.le_normalizer
      (inf_le_right.trans (hCB.trans (Subgroup.centralizer_le_normalizer (B : Set Ω))))
  exact (ne_of_lt hmaxB.1)
    (hnormal B (isUniqueMaxOver_iff.mp hB).2.1 hmaxB.le hLnormB)

private lemma conjIntersection_sup_ne {G L S B : Subgroup Ω}
    (hLG : L ≤ G) (hSG : S ≤ G)
    (hG' : conjSup(G, L) ⊔ S = G)
    (hSN : S ≤ Subgroup.normalizer ((conjSup(G, L) : Subgroup Ω) : Set Ω))
    (hcomm : ∀ g ∈ G, conjSub g L ≠ L → ⁅L, conjSub g L⁆ = ⊥)
    (hB : IsUniqueMaxOver L (S ⊓ L) B)
    (hnormal : ∀ K : Subgroup Ω, S ⊓ L ≤ K → K ≤ L →
      L ≤ Subgroup.normalizer (K : Set Ω) → K = L)
    (hSltG : S < G)
    (hDleBC : conjIntersection(S, B, otherConjSup(G, L)) ≤ B ⊔ otherConjSup(G, L))
    (hDset : (↑(conjIntersection(S, B, otherConjSup(G, L)) ⊔ S) : Set Ω) =
      ((conjIntersection(S, B, otherConjSup(G, L)) : Subgroup Ω) : Set Ω) * (↑S : Set Ω)) :
    conjIntersection(S, B, otherConjSup(G, L)) ⊔ S ≠ G := by
  intro hMG
  exact not_conjSup_le_sup hcomm hB hnormal
    (conjSup_le_sup_of_sup_eq hLG hSG hG' hSN hcomm hB hnormal hSltG hDleBC hDset hMG)

omit [Finite Ω] in
private lemma isUniqueMaxOver_of_hover {G S M : Subgroup Ω}
    (hMltG : M < G) (hSM : S ≤ M)
    (hover : ∀ H : Subgroup Ω, S ≤ H → H < G → H ≤ M) :
    IsUniqueMaxOver G S M := by
  refine isUniqueMaxOver_iff.mpr ⟨⟨hMltG, ?_⟩, hSM, ?_⟩
  · intro K hMK hKG
    by_contra hKGne
    have hKltG : K < G := lt_of_le_of_ne hKG hKGne
    have hKM : K ≤ M := hover K (hSM.trans hMK.le) hKltG
    exact (not_le_of_gt hMK) hKM
  · intro K hKmax hSK
    by_cases hKM : K = M
    · exact hKM
    · exfalso
      have hKleM : K ≤ M := hover K hSK hKmax.1
      have hKltM : K < M := lt_of_le_of_ne hKleM hKM
      exact (ne_of_lt hMltG) (hKmax.2 M hKltM hMltG.le)

theorem exists_isUniqueMaxOver_of_commute_conj {G L S B : Subgroup Ω}
    (hLG : L ≤ G) (hSG : S ≤ G)
    (hcomm : ∀ g ∈ G, L.map (MulAut.conj g).toMonoidHom ≠ L →
      ⁅L, L.map (MulAut.conj g).toMonoidHom⁆ = ⊥)
    (hG : (⨆ g ∈ G, L.map (MulAut.conj g).toMonoidHom) ⊔ S = G)
    (hB : IsUniqueMaxOver L (S ⊓ L) B)
    (hnormal : ∀ K : Subgroup Ω, S ⊓ L ≤ K → K ≤ L → L ≤ Subgroup.normalizer (K : Set Ω) →
      K = L) :
    ∃ M : Subgroup Ω, IsUniqueMaxOver G S M := by
  have hcomm' := commute_conjSub_form hcomm
  have hG' := conjSup_sup_eq hG
  have hSN := le_normalizer_conjSup (L := L) hSG
  have hSltG := lt_of_isUniqueMaxOver_inf hLG hSG hB
  have hDleBC : conjIntersection(S, B, otherConjSup(G, L)) ≤ B ⊔ otherConjSup(G, L) :=
    conjIntersection_le S B (otherConjSup(G, L))
  have hDleN : conjIntersection(S, B, otherConjSup(G, L)) ≤ conjSup(G, L) :=
    hDleBC.trans (sup_le ((isUniqueMaxOver_iff.mp hB).1.le.trans (le_conjSup G L))
      (otherConjSup_le_conjSup G L))
  have hDset : (↑(conjIntersection(S, B, otherConjSup(G, L)) ⊔ S) : Set Ω) =
      ((conjIntersection(S, B, otherConjSup(G, L)) : Subgroup Ω) : Set Ω) * (↑S : Set Ω) :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ S
      (le_normalizer_conjIntersection S B (otherConjSup(G, L)))
  set M : Subgroup Ω := conjIntersection(S, B, otherConjSup(G, L)) ⊔ S with hMdef
  have hover : ∀ H : Subgroup Ω, S ≤ H → H < G → H ≤ M := by
    intro H hSH hHG
    rw [hMdef]
    exact le_sup_of_le_conjIntersection hG' hSN hSH hHG
      (le_conjIntersection hSG hG' hSN hcomm' hB hnormal hSH hHG)
  have hMleG : M ≤ G := by
    rw [hMdef]
    exact sup_le (hDleN.trans (conjSup_le hLG)) hSG
  have hMproper : M ≠ G := by
    rw [hMdef]
    exact conjIntersection_sup_ne hLG hSG hG' hSN hcomm' hB hnormal hSltG hDleBC hDset
  have hMltG : M < G := lt_of_le_of_ne hMleG hMproper
  exact ⟨M, isUniqueMaxOver_of_hover hMltG
    (by rw [hMdef]; exact le_sup_right) hover⟩

end Existence

section Comap

variable [Group Ω] {Y : Type*} [Group Y]

private lemma comap_ker_le {G : Subgroup Ω} {φ : ↥G →* Y} {M : Subgroup Y} :
    φ.ker.map G.subtype ≤ (M.comap φ).map G.subtype := by
  rintro x ⟨k, hk, rfl⟩
  exact Subgroup.mem_map_of_mem G.subtype (by
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hk]
    exact M.one_mem)

private lemma le_comap_map {G S : Subgroup Ω} {φ : ↥G →* Y} {M : Subgroup Y}
    (hSG : S ≤ G) (hSM : (S.subgroupOf G).map φ ≤ M) :
    S ≤ (M.comap φ).map G.subtype := by
  intro s hs
  refine Subgroup.mem_map_of_mem (f := G.subtype) (x := (⟨s, hSG hs⟩ : ↥G)) ?_
  rw [Subgroup.mem_comap]
  exact hSM (Subgroup.mem_map_of_mem φ (Subgroup.mem_subgroupOf.mpr hs))

private lemma comap_lt_top {G : Subgroup Ω} {φ : ↥G →* Y} {M : Subgroup Y}
    (hMmax : IsMaxSubgroupIn φ.range M) :
    (M.comap φ).map G.subtype < G := by
  refine lt_of_le_of_ne (Subgroup.map_subtype_le _) ?_
  intro hEq
  obtain ⟨y, hyrange, hyM⟩ := (SetLike.lt_iff_le_and_exists.mp hMmax.1).2
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hyrange
  have hxM' : (x : Ω) ∈ (M.comap φ).map G.subtype := by rw [hEq]; exact x.2
  obtain ⟨c, hc, hcx⟩ := Subgroup.mem_map.mp hxM'
  have hc_eq : c = x := Subtype.ext hcx
  rw [hc_eq] at hc
  exact hyM (Subgroup.mem_comap.mp hc)

private lemma comap_max {G : Subgroup Ω} {φ : ↥G →* Y} {M : Subgroup Y}
    (hMmax : IsMaxSubgroupIn φ.range M)
    (hkerM' : φ.ker.map G.subtype ≤ (M.comap φ).map G.subtype) :
    IsMaxSubgroupIn G ((M.comap φ).map G.subtype) := by
  refine ⟨comap_lt_top hMmax, ?_⟩
  intro K hM'K hKG
  let K' : Subgroup ↥G := K.subgroupOf G
  have hkerK' : φ.ker ≤ K' := by
    intro k hk
    exact Subgroup.mem_subgroupOf.mpr
      (hM'K.le (hkerM' (Subgroup.mem_map_of_mem G.subtype hk)))
  have hK'eq : (Subgroup.map φ K').comap φ = K' := Subgroup.comap_map_eq_self hkerK'
  have hMleφK : M ≤ Subgroup.map φ K' := by
    have hMcomap : M.comap φ ≤ K' := by
      intro c hc
      exact Subgroup.mem_subgroupOf.mpr
        (hM'K.le (Subgroup.mem_map_of_mem G.subtype hc))
    calc M = (M.comap φ).map φ := (Subgroup.map_comap_eq_self hMmax.le).symm
      _ ≤ Subgroup.map φ K' := Subgroup.map_mono hMcomap
  by_cases hφK : Subgroup.map φ K' = M
  · exfalso
    have hK'M : K' ≤ M.comap φ := by
      rw [← hφK, hK'eq]
    have hKM' : K ≤ (M.comap φ).map G.subtype := by
      have h := Subgroup.map_mono (f := G.subtype) hK'M
      rwa [Subgroup.map_subgroupOf_eq_of_le hKG] at h
    exact (ne_of_lt hM'K) (le_antisymm hM'K.le hKM')
  · have hMltφK : M < Subgroup.map φ K' :=
      lt_of_le_of_ne hMleφK (fun hEq => hφK hEq.symm)
    have hφKrange : Subgroup.map φ K' = φ.range :=
      hMmax.2 (Subgroup.map φ K') hMltφK (Subgroup.map_le_range φ K')
    apply le_antisymm hKG
    intro g hg
    have hφg : φ ⟨g, hg⟩ ∈ Subgroup.map φ K' := by
      rw [hφKrange]
      exact MonoidHom.mem_range.mpr ⟨⟨g, hg⟩, rfl⟩
    obtain ⟨k', hk', hk'g⟩ := Subgroup.mem_map.mp hφg
    have hmemker : k'⁻¹ * (⟨g, hg⟩ : ↥G) ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hk'g, inv_mul_cancel]
    have hmemK' : k'⁻¹ * (⟨g, hg⟩ : ↥G) ∈ K' := hkerK' hmemker
    have hgK' : (⟨g, hg⟩ : ↥G) ∈ K' := by
      have h := K'.mul_mem hk' hmemK'
      rwa [show k' * (k'⁻¹ * (⟨g, hg⟩ : ↥G)) = ⟨g, hg⟩ by group] at h
    exact Subgroup.mem_subgroupOf.mp hgK'

private lemma map_subgroupOf_lt_range {G : Subgroup Ω} {φ : ↥G →* Y} {H : Subgroup Ω}
    (hHmax : IsMaxSubgroupIn G H) (hkerH' : φ.ker ≤ H.subgroupOf G) :
    Subgroup.map φ (H.subgroupOf G) < φ.range := by
  refine lt_of_le_of_ne (Subgroup.map_le_range φ _) ?_
  intro hEq
  have hH'top : H.subgroupOf G = ⊤ := by
    have h1 : (Subgroup.map φ (H.subgroupOf G)).comap φ = H.subgroupOf G :=
      Subgroup.comap_map_eq_self hkerH'
    have hcomap : (φ.range).comap φ = ⊤ := by
      ext x
      simp
    rw [hEq, hcomap] at h1
    exact h1.symm
  have hHG : H = G := by
    have h := congrArg (Subgroup.map G.subtype) hH'top
    rw [Subgroup.map_subgroupOf_eq_of_le hHmax.le, Subgroup.map_top,
      Subgroup.range_subtype] at h
    exact h
  exact (ne_of_lt hHmax.1) hHG

private lemma map_subgroupOf_max {G : Subgroup Ω} {φ : ↥G →* Y} {H : Subgroup Ω}
    (hHmax : IsMaxSubgroupIn G H) (hkerH' : φ.ker ≤ H.subgroupOf G) :
    IsMaxSubgroupIn φ.range (Subgroup.map φ (H.subgroupOf G)) := by
  refine ⟨map_subgroupOf_lt_range hHmax hkerH', ?_⟩
  intro U hU hUle
  obtain ⟨y, hyU, hyNot⟩ := (SetLike.lt_iff_le_and_exists.mp hU).2
  obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp (hUle hyU)
  let K : Subgroup Ω := (U.comap φ).map G.subtype
  have hHKle : H ≤ K := by
    intro h hh
    have hhG : h ∈ G := hHmax.le hh
    have hmemH' : (⟨h, hhG⟩ : ↥G) ∈ H.subgroupOf G := Subgroup.mem_subgroupOf.mpr hh
    have hφ : φ ⟨h, hhG⟩ ∈ Subgroup.map φ (H.subgroupOf G) :=
      Subgroup.mem_map_of_mem φ hmemH'
    show h ∈ (U.comap φ).map G.subtype
    exact Subgroup.mem_map_of_mem (f := G.subtype) (x := (⟨h, hhG⟩ : ↥G))
      (Subgroup.mem_comap.mpr (hU.le hφ))
  have hgK : G.subtype g ∈ K :=
    Subgroup.mem_map_of_mem G.subtype (Subgroup.mem_comap.mpr hyU)
  have hgH : G.subtype g ∉ H := by
    intro hmem
    exact hyNot (Subgroup.mem_map_of_mem φ (Subgroup.mem_subgroupOf.mpr hmem))
  have hHK : H < K := lt_of_le_of_ne hHKle (by intro hEq; exact hgH (hEq ▸ hgK))
  have hKG : K = G := hHmax.2 K hHK (Subgroup.map_subtype_le _)
  apply le_antisymm hUle
  intro y hy
  obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hy
  have hgG : G.subtype g ∈ K := by rw [hKG]; exact g.2
  obtain ⟨c, hc, hcg⟩ := Subgroup.mem_map.mp hgG
  have hc_eq : c = g := Subtype.ext hcg
  rw [hc_eq] at hc
  exact Subgroup.mem_comap.mp hc

private lemma comap_eq_of_map_eq {G : Subgroup Ω} {φ : ↥G →* Y} {M : Subgroup Y}
    {H : Subgroup Ω} (hHmax : IsMaxSubgroupIn G H) (hkerH' : φ.ker ≤ H.subgroupOf G)
    (hH'M : Subgroup.map φ (H.subgroupOf G) = M) :
    H = (M.comap φ).map G.subtype := by
  have hH'eq : H.subgroupOf G = M.comap φ := by
    rw [← hH'M]
    exact (Subgroup.comap_map_eq_self hkerH').symm
  calc H = (H.subgroupOf G).map G.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hHmax.le).symm
    _ = (M.comap φ).map G.subtype := by rw [hH'eq]

private lemma comap_eq {G S : Subgroup Ω} {φ : ↥G →* Y} {M : Subgroup Y}
    (hker : ∀ H : Subgroup Ω, IsMaxSubgroupIn G H → S ≤ H → φ.ker.map G.subtype ≤ H)
    (huniq : ∀ N : Subgroup Y, IsMaxSubgroupIn φ.range N →
      (S.subgroupOf G).map φ ≤ N → N = M)
    {H : Subgroup Ω} (hHmax : IsMaxSubgroupIn G H) (hSH : S ≤ H) :
    H = (M.comap φ).map G.subtype := by
  have hkerH : φ.ker.map G.subtype ≤ H := hker H hHmax hSH
  have hkerH' : φ.ker ≤ H.subgroupOf G := by
    intro k hk
    exact Subgroup.mem_subgroupOf.mpr (hkerH (Subgroup.mem_map_of_mem G.subtype hk))
  have hH'max : IsMaxSubgroupIn φ.range (Subgroup.map φ (H.subgroupOf G)) :=
    map_subgroupOf_max hHmax hkerH'
  have hSmap : (S.subgroupOf G).map φ ≤ Subgroup.map φ (H.subgroupOf G) := by
    intro y hy
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hy
    exact Subgroup.mem_map_of_mem φ
      (Subgroup.mem_subgroupOf.mpr (hSH (Subgroup.mem_subgroupOf.mp hs)))
  exact comap_eq_of_map_eq hHmax hkerH' (huniq _ hH'max hSmap)

theorem isUniqueMaxOver_comap_of_ker_le {G S : Subgroup Ω}
    (hSG : S ≤ G) (φ : ↥G →* Y)
    (hker : ∀ H : Subgroup Ω, IsMaxSubgroupIn G H → S ≤ H → φ.ker.map G.subtype ≤ H)
    {M : Subgroup Y} (h : IsUniqueMaxOver φ.range ((S.subgroupOf G).map φ) M) :
    IsUniqueMaxOver G S ((M.comap φ).map G.subtype) := by
  obtain ⟨hMmax, hSM, huniq⟩ := isUniqueMaxOver_iff.mp h
  have hkerM' : φ.ker.map G.subtype ≤ (M.comap φ).map G.subtype := comap_ker_le
  have hSM' : S ≤ (M.comap φ).map G.subtype := le_comap_map hSG hSM
  have hMmax' : IsMaxSubgroupIn G ((M.comap φ).map G.subtype) :=
    comap_max hMmax hkerM'
  exact isUniqueMaxOver_iff.mpr ⟨hMmax', hSM', fun H hHmax hSH =>
    comap_eq hker huniq hHmax hSH⟩

end Comap

end CFSG.GroupTheory
