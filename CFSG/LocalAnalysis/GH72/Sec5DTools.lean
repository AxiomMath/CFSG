module

public import CFSG.LocalAnalysis.GH72.Sec5DBasic
public import CFSG.GroupTheory.CentralSylowComplement
public import CFSG.LocalAnalysis.GH72.OuterFacts

public section

namespace CFSG.GH72

open Subgroup
open scoped Pointwise commutatorElement

namespace G5d

section Permutable

variable {G : Type*} [Group G]

theorem coe_sup_eq_mul_of_mul_comm {H K : Subgroup G}
    (h : (H : Set G) * (K : Set G) = (K : Set G) * (H : Set G)) :
    ((H ⊔ K : Subgroup G) : Set G) = (H : Set G) * (K : Set G) := by
  have hmul : ∀ x ∈ (H : Set G) * (K : Set G), ∀ y ∈ (H : Set G) * (K : Set G),
      x * y ∈ (H : Set G) * (K : Set G) := by
    rintro _ ⟨a₁, ha₁, b₁, hb₁, rfl⟩ _ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
    have hba : b₁ * a₂ ∈ (H : Set G) * (K : Set G) := by
      rw [h]
      exact ⟨b₁, hb₁, a₂, ha₂, rfl⟩
    obtain ⟨a', ha', b', hb', hab⟩ := hba
    have hab' : a' * b' = b₁ * a₂ := hab
    refine ⟨a₁ * a', H.mul_mem ha₁ ha', b' * b₂, K.mul_mem hb' hb₂, ?_⟩
    calc a₁ * a' * (b' * b₂) = a₁ * (a' * b') * b₂ := by group
      _ = a₁ * (b₁ * a₂) * b₂ := by rw [hab']
      _ = a₁ * b₁ * (a₂ * b₂) := by group
  have hinv : ∀ x ∈ (H : Set G) * (K : Set G), x⁻¹ ∈ (H : Set G) * (K : Set G) := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    rw [h, mul_inv_rev]
    exact ⟨b⁻¹, K.inv_mem hb, a⁻¹, H.inv_mem ha, rfl⟩
  let S : Subgroup G :=
    { carrier := (H : Set G) * (K : Set G)
      mul_mem' := fun {x y} hx hy => hmul x hx y hy
      one_mem' := ⟨1, H.one_mem, 1, K.one_mem, one_mul 1⟩
      inv_mem' := fun {x} hx => hinv x hx }
  apply le_antisymm
  · have hle : H ⊔ K ≤ S := sup_le (fun x hx => ⟨x, hx, 1, K.one_mem, mul_one x⟩)
      (fun x hx => ⟨1, H.one_mem, x, hx, one_mul x⟩)
    exact hle
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    exact mul_mem_sup ha hb

theorem mem_sup_of_mul_comm {H K : Subgroup G}
    (h : (H : Set G) * (K : Set G) = (K : Set G) * (H : Set G)) {g : G} (hg : g ∈ H ⊔ K) :
    ∃ a ∈ H, ∃ b ∈ K, a * b = g := by
  have hg' : g ∈ ((H ⊔ K : Subgroup G) : Set G) := hg
  rw [coe_sup_eq_mul_of_mul_comm h] at hg'
  obtain ⟨a, ha, b, hb, rfl⟩ := hg'
  exact ⟨a, ha, b, hb, rfl⟩

theorem le_normalizer_commutator_of_mul_comm [Finite G] {T P X : Subgroup G}
    (hPX : P ≤ centralizer (X : Set G))
    (hTP : (T : Set G) * (P : Set G) = (P : Set G) * (T : Set G)) :
    P ≤ normalizer ((⁅T, X⁆ : Subgroup G) : Set G) := by
  have hle : ⁅T ⊔ P, X⁆ ≤ ⁅T, X⁆ := by
    rw [commutator_le]
    intro g hg x hx
    obtain ⟨t, ht, q, hq, rfl⟩ := mem_sup_of_mul_comm hTP hg
    have hqx : q * x = x * q := mem_centralizer_iff.mp (hPX hq) x hx |>.symm
    have : ⁅t * q, x⁆ = ⁅t, x⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      calc t * q * x * (t * q)⁻¹ * x⁻¹ = t * (q * x) * q⁻¹ * t⁻¹ * x⁻¹ := by group
        _ = t * (x * q) * q⁻¹ * t⁻¹ * x⁻¹ := by rw [hqx]
        _ = t * x * t⁻¹ * x⁻¹ := by group
    rw [this]
    exact commutator_mem_commutator ht hx
  have heq : ⁅T ⊔ P, X⁆ = ⁅T, X⁆ := le_antisymm hle (commutator_mono le_sup_left le_rfl)
  intro q hq
  rw [← heq]
  exact normalizer_commutator_ge_left (T ⊔ P) X (mem_sup_right hq)

end Permutable

section Conj

variable {G : Type*} [Group G] [Finite G]

theorem mem_normalizer_of_map_conj_le {H : Subgroup G} {g : G}
    (h : H.map (MulAut.conj g).toMonoidHom ≤ H) : g ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq]
  exact eq_of_le_of_card_ge h (by rw [card_map_of_injective (MulAut.conj g).injective])

theorem map_conj_le_normalizer_map {H K : Subgroup G} (hK : K ≤ normalizer (H : Set G)) (g : G) :
    K.map (MulAut.conj g).toMonoidHom ≤
      normalizer ((H.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  rintro _ ⟨k, hk, rfl⟩
  refine mem_normalizer_of_map_conj_le (le_of_eq ?_)
  have hk' : H.map (MulAut.conj k).toMonoidHom = H := G4b.mem_normalizer_iff_map_conj_eq'.mp (hK hk)
  calc (H.map (MulAut.conj g).toMonoidHom).map
        (MulAut.conj ((MulAut.conj g).toMonoidHom k)).toMonoidHom
      = H.map (MulAut.conj (g * k)).toMonoidHom := by
        rw [G4b.map_conj_map_conj]
        congr 3
        change g * k * g⁻¹ * g = g * k
        group
    _ = (H.map (MulAut.conj k).toMonoidHom).map (MulAut.conj g).toMonoidHom :=
        (G4b.map_conj_map_conj H k g).symm
    _ = H.map (MulAut.conj g).toMonoidHom := by rw [hk']

theorem card_le_of_isSylowOf {p : ℕ} [Fact p.Prime] {S K R : Subgroup G}
    (hS : ABGLocalTools.IsSylowOf p S K) (hRK : R ≤ K) (hR : IsPGroup p R) :
    Nat.card R ≤ Nat.card S := by
  obtain ⟨c, -, hc⟩ := exists_mem_map_conj_le_of_isSylowOf hS hRK hR
  calc Nat.card R = Nat.card (R.map (MulAut.conj c).toMonoidHom) :=
        (card_map_of_injective (MulAut.conj c).injective).symm
    _ ≤ Nat.card S := card_le_of_le hc

end Conj

section CentralizerMod

variable {G : Type*} [Group G] [Finite G]

private def centralizerMod (K S N : Subgroup G) (hKN : K ≤ normalizer (N : Set G)) :
    Subgroup G where
  carrier := {k | k ∈ K ∧ ∀ s ∈ S, k * s * k⁻¹ * s⁻¹ ∈ N}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨K.mul_mem ha hb, fun s hs => ?_⟩
    have h1 : a * b * s * (a * b)⁻¹ * s⁻¹ =
        (a * (b * s * b⁻¹ * s⁻¹) * a⁻¹) * (a * s * a⁻¹ * s⁻¹) := by group
    rw [h1]
    exact N.mul_mem ((mem_normalizer_iff.mp (hKN ha) _).mp (hb' s hs)) (ha' s hs)
  one_mem' := ⟨K.one_mem, fun s _ => by simp⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨K.inv_mem ha, fun s hs => ?_⟩
    have h1 : a⁻¹ * s * a⁻¹⁻¹ * s⁻¹ = a⁻¹ * (a * s * a⁻¹ * s⁻¹)⁻¹ * a := by group
    rw [h1]
    have := (mem_normalizer_iff.mp (hKN (K.inv_mem ha)) _).mp (N.inv_mem (ha' s hs))
    simpa [mul_assoc] using this

theorem le_O_of_commutator_mem_O {Z W M₀ D : Subgroup G} (hZ2 : IsPGroup 2 Z)
    (hZc : Z ≤ centralizer (Z : Set G)) (hW2 : IsPGroup 2 W) (hWZ : W ≤ centralizer (Z : Set G))
    (hWc : W ≤ centralizer (W : Set G)) (hZW : Z ⊓ W = ⊥)
    (hsyl : ABGLocalTools.IsSylowOf 2 (Z ⊔ W) (centralizer ((Z ⊔ W : Subgroup G) : Set G)))
    (hM₀ : M₀ ≤ centralizer (Z : Set G))
    (hMM₀ : centralizer (Z : Set G) ≤ normalizer (M₀ : Set G))
    (hWM₀ : W ≤ M₀)
    (hcen : ∀ m ∈ M₀, (∀ m' ∈ M₀, m * m' * m⁻¹ * m'⁻¹ ∈ O (centralizer (Z : Set G))) →
      m ∈ O (centralizer (Z : Set G)))
    (hDM : D ≤ centralizer (Z : Set G)) (hD : Odd (Nat.card D))
    (hDc : ∀ d ∈ D, ∀ m ∈ M₀, d * m * d⁻¹ * m⁻¹ ∈ O (centralizer (Z : Set G))) :
    D ≤ O (centralizer (Z : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M : Subgroup G := centralizer (Z : Set G) with hMdef
  set OM : Subgroup G := O M with hOMdef
  have hMOM : M ≤ normalizer (OM : Set G) := le_normalizer_O M
  set Cs : Subgroup G := centralizerMod M M₀ OM hMOM with hCs
  have hCsM : Cs ≤ M := fun c hc => hc.1
  have hOModd : Odd (Nat.card OM) := card_O_odd M
  have h2odd : ∀ {B : Subgroup G}, IsPGroup 2 B → B ⊓ OM = ⊥ := by
    intro B hB
    rcases (hB.to_inf_left (K := OM)).card_eq_or_dvd with h1 | h2
    · exact card_eq_one.mp h1
    · exact absurd (h2.trans (card_dvd_of_le inf_le_right))
        (Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hOModd))
  have hMCs : M ≤ normalizer (Cs : Set G) := by
    intro m hm
    refine mem_normalizer_of_map_conj_le ?_
    rintro _ ⟨c, ⟨hcM, hc⟩, rfl⟩
    refine ⟨M.mul_mem (M.mul_mem hm hcM) (M.inv_mem hm), fun s hs => ?_⟩
    change m * c * m⁻¹ * s * (m * c * m⁻¹)⁻¹ * s⁻¹ ∈ OM
    have hs' : m⁻¹ * s * m ∈ M₀ := by
      have := (mem_normalizer_iff.mp (hMM₀ (M.inv_mem hm)) s).mp hs
      simpa using this
    have h1 : m * c * m⁻¹ * s * (m * c * m⁻¹)⁻¹ * s⁻¹ =
        m * (c * (m⁻¹ * s * m) * c⁻¹ * (m⁻¹ * s * m)⁻¹) * m⁻¹ := by group
    rw [h1]
    exact (mem_normalizer_iff.mp (hMOM hm) _).mp (hc _ hs')
  have hCsM₀ : Cs ⊓ M₀ ≤ OM := fun m ⟨hm, hm₀⟩ => hcen m hm₀ hm.2
  have hZM : Z ≤ M := hZc
  have hZCs : Z ≤ Cs := by
    intro z hz
    refine ⟨hZM hz, fun s hs => ?_⟩
    have hzs : z * s = s * z := mem_centralizer_iff.mp (hM₀ hs) z hz
    rw [hzs]
    simp
  have hDCs : D ≤ Cs := fun d hd => ⟨hDM hd, hDc d hd⟩
  have hWM : W ≤ M := hWZ
  have hWOM : W ≤ normalizer (OM : Set G) := hWM.trans hMOM
  set K : Subgroup G := OM ⊔ W with hKdef
  have hOMW : OM ⊓ W = ⊥ := by rw [inf_comm]; exact h2odd hW2
  have hKcard : Nat.card K = Nat.card OM * Nat.card W :=
    CFSG.CGT.Foote81L6.card_sup_of_le_normalizer hWOM hOMW
  have hWK : ABGLocalTools.IsSylowOf 2 W K := by
    rw [ABGLocalTools.isSylowOf_iff]
    refine ⟨le_sup_right, hW2, fun h2 => ?_⟩
    have h1 := Subgroup.relIndex_mul_card W K
    rw [inf_eq_left.mpr (le_sup_right : W ≤ K), hKcard] at h1
    have h3 : W.relIndex K = Nat.card OM := Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
    rw [h3] at h2
    exact (Nat.not_even_iff_odd.mpr hOModd) (even_iff_two_dvd.mpr h2)
  have hkey : ∀ B : Subgroup G, B ≤ Cs → IsPGroup 2 B → Z ≤ B → Nat.card B ≤ Nat.card Z := by
    intro B hBCs hB2 hZB
    have hBK : B ≤ normalizer (K : Set G) := by
      intro b hb
      refine mem_normalizer_of_map_conj_le ?_
      rw [hKdef, Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rw [G4b.mem_normalizer_iff_map_conj_eq'.mp (hMOM (hCsM (hBCs hb)))]
        exact le_sup_left
      · rintro _ ⟨w, hw, rfl⟩
        change b * w * b⁻¹ ∈ OM ⊔ W
        have : b * w * b⁻¹ = (b * w * b⁻¹ * w⁻¹) * w := by group
        rw [this]
        exact mul_mem_sup ((hBCs hb).2 w (hWM₀ hw)) hw
    set H' : Subgroup G := K ⊔ B with hH'
    have hH'K : H' ≤ normalizer (K : Set G) := sup_le le_normalizer hBK
    obtain ⟨R₀, hR₀⟩ := (hB2.comap_subtype (K := H')).exists_le_sylow
    set R : Subgroup G := (R₀ : Subgroup H').map H'.subtype with hR
    have hRsyl : ABGLocalTools.IsSylowOf 2 R H' := ⟨R₀, rfl⟩
    have hBR : B ≤ R := fun b hb =>
      ⟨⟨b, mem_sup_right hb⟩, hR₀ (show (⟨b, mem_sup_right hb⟩ : H') ∈ B.comap H'.subtype from hb),
        rfl⟩
    have hS : ABGLocalTools.IsSylowOf 2 (R ⊓ K) K := hRsyl.inf_of_le_normalizer le_sup_left hH'K
    have hBS : B ≤ normalizer ((R ⊓ K : Subgroup G) : Set G) := fun b hb =>
      inf_normalizer_le_normalizer_inf ⟨le_normalizer (hBR hb), hBK hb⟩
    obtain ⟨c, hcK, hc⟩ := exists_mem_map_conj_le_of_isSylowOf hWK hS.le hS.isPGroup
    have hcW : (R ⊓ K).map (MulAut.conj c).toMonoidHom = W :=
      eq_of_le_of_card_ge hc (by
        rw [card_map_of_injective (MulAut.conj c).injective, hS.card_eq, hWK.card_eq])
    obtain ⟨w, hw, o, ho, rfl⟩ := mem_sup_of_le_normalizer' hWOM
      (show c ∈ W ⊔ OM by rw [sup_comm]; exact hcK)
    have hoW : (R ⊓ K).map (MulAut.conj o).toMonoidHom = W := by
      have h1 := congrArg (map (MulAut.conj w⁻¹).toMonoidHom) hcW
      rwa [G4b.map_conj_map_conj, show w⁻¹ * (w * o) = o by group,
        G4b.mem_normalizer_iff_map_conj_eq'.mp (le_normalizer (W.inv_mem hw))] at h1
    set B' : Subgroup G := B.map (MulAut.conj o).toMonoidHom with hB'
    have hoM : o ∈ M := (map_subtype_le _ : OM ≤ M) ho
    have hB'W : B' ≤ normalizer (W : Set G) := by
      have := map_conj_le_normalizer_map hBS o
      rwa [hoW] at this
    have hB'Cs : B' ≤ Cs := by
      rw [hB', ← G4b.mem_normalizer_iff_map_conj_eq'.mp (hMCs hoM)]
      exact map_mono hBCs
    have hB'2 : IsPGroup 2 B' := hB2.map _
    have hZB' : Z ≤ B' := by
      intro z hz
      refine ⟨z, hZB hz, ?_⟩
      change o * z * o⁻¹ = z
      have := mem_centralizer_iff.mp hoM z hz
      rw [← this]
      group
    have hB'cW : B' ≤ centralizer (W : Set G) := by
      intro b hb
      rw [mem_centralizer_iff]
      intro u hu
      have h1 : b * u * b⁻¹ * u⁻¹ ∈ W ⊓ OM :=
        ⟨W.mul_mem ((mem_normalizer_iff.mp (hB'W hb) u).mp hu) (W.inv_mem hu),
          (hB'Cs hb).2 u (hWM₀ hu)⟩
      rw [inf_comm, hOMW, mem_bot] at h1
      have : b * u = u * b := by
        calc b * u = (b * u * b⁻¹ * u⁻¹) * u * b := by group
          _ = u * b := by rw [h1, one_mul]
      exact this.symm
    have hB'Winf : B' ⊓ W = ⊥ := by
      have hle : B' ⊓ W ≤ OM := fun x hx => hCsM₀ ⟨hB'Cs hx.1, hWM₀ hx.2⟩
      have h0 := h2odd (hB'2.to_le (inf_le_left : B' ⊓ W ≤ B'))
      rwa [inf_eq_left.mpr hle] at h0
    have hWB' : W ≤ normalizer (B' : Set G) :=
      CFSG.CGT.Foote81L6.le_normalizer_of_comm fun b hb u hu =>
        (mem_centralizer_iff.mp (hB'cW hb) u hu).symm
    have hB'W2 : IsPGroup 2 (B' ⊔ W : Subgroup G) := IsPGroup.to_sup_of_normal_left' hB'2 hW2 hWB'
    have hB'Wcard : Nat.card (B' ⊔ W : Subgroup G) = Nat.card B' * Nat.card W :=
      CFSG.CGT.Foote81L6.card_sup_of_le_normalizer hWB' hB'Winf
    have hcentA : ∀ {X₀ : Subgroup G}, X₀ ≤ centralizer (Z : Set G) →
        X₀ ≤ centralizer (W : Set G) → X₀ ≤ centralizer ((Z ⊔ W : Subgroup G) : Set G) := by
      intro X₀ h₁ h₂
      rw [le_centralizer_iff] at h₁ h₂ ⊢
      exact sup_le h₁ h₂
    have hB'WA : B' ⊔ W ≤ centralizer ((Z ⊔ W : Subgroup G) : Set G) :=
      sup_le (hcentA (hB'Cs.trans hCsM) hB'cW) (hcentA hWZ hWc)
    have hle := card_le_of_isSylowOf hsyl hB'WA hB'W2
    have hZWcard : Nat.card (Z ⊔ W : Subgroup G) = Nat.card Z * Nat.card W :=
      CFSG.CGT.Foote81L6.card_sup_of_le_normalizer
        (CFSG.CGT.Foote81L6.le_normalizer_of_comm fun z hz u hu =>
          mem_centralizer_iff.mp (hWZ hu) z hz) hZW
    rw [hB'Wcard, hZWcard] at hle
    have hBB' : Nat.card B' = Nat.card B := card_map_of_injective (MulAut.conj o).injective
    rw [hBB'] at hle
    exact Nat.le_of_mul_le_mul_right hle Nat.card_pos
  have hZsyl : ABGLocalTools.IsSylowOf 2 Z Cs := by
    obtain ⟨R₀, hR₀⟩ := ABGLocalTools.exists_isSylowOf 2 Cs
    obtain ⟨c, hcCs, hc⟩ := exists_mem_map_conj_le_of_isSylowOf hR₀ hZCs hZ2
    set B : Subgroup G := R₀.map (MulAut.conj c⁻¹).toMonoidHom with hB
    have hZB : Z ≤ B := by
      have h1 := map_mono (f := (MulAut.conj c⁻¹).toMonoidHom) hc
      rwa [G4b.map_conj_map_conj, inv_mul_cancel, G4b.map_conj_one] at h1
    have hBCs : B ≤ Cs := by
      rw [hB, ← G4b.mem_normalizer_iff_map_conj_eq'.mp (le_normalizer (Cs.inv_mem hcCs))]
      exact map_mono hR₀.le
    have hBcard : Nat.card B = Nat.card R₀ := card_map_of_injective (MulAut.conj c⁻¹).injective
    have h1 := hkey B hBCs (hR₀.isPGroup.map _) hZB
    rw [hBcard] at h1
    have h2 := card_le_of_isSylowOf hR₀ hZCs hZ2
    exact ABGLocalTools.isSylowOf_of_card hZCs (by rw [le_antisymm h2 h1]; exact hR₀.card_eq)
  obtain ⟨O', hO'Cs, hO', -, -⟩ := CFSG.GroupTheory.exists_complement_of_central_sylow hZCs hZ2
    (fun x hx q hq => (mem_centralizer_iff.mp (hCsM hx) q hq).symm)
    ((ABGLocalTools.isSylowOf_iff.mp hZsyl).2.2)
  have hDO' : D ≤ O' := by
    intro d hd
    refine (hO' d (hDCs hd)).mpr fun h2 => ?_
    have h3 : orderOf d ∣ Nat.card D := Subgroup.orderOf_dvd_natCard D hd
    exact (Nat.not_even_iff_odd.mpr hD) (even_iff_two_dvd.mpr (h2.trans h3))
  have hO'odd : Odd (Nat.card O') := by
    rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    intro h2
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := O') 2 h2
    have hx' : orderOf (x : G) = 2 := by rw [Subgroup.orderOf_coe, hx]
    exact (hO' x (hO'Cs x.2)).mp x.2 (by rw [hx'])
  have hMO' : M ≤ normalizer (O' : Set G) := by
    intro m hm
    refine mem_normalizer_of_map_conj_le ?_
    rintro _ ⟨x, hx, rfl⟩
    have hxCs : (MulAut.conj m).toMonoidHom x ∈ Cs := by
      rw [← G4b.mem_normalizer_iff_map_conj_eq'.mp (hMCs hm)]
      exact ⟨x, hO'Cs hx, rfl⟩
    refine (hO' _ hxCs).mpr ?_
    change ¬ 2 ∣ orderOf (m * x * m⁻¹)
    rw [orderOf_conj_eq]
    exact (hO' x (hO'Cs hx)).mp hx
  exact hDO'.trans (le_O_of_le_normalizer (hO'Cs.trans hCsM) hMO' hO'odd)

end CentralizerMod

section Joins

variable {G : Type*} [Group G] [Finite G]

theorem le_normalizer_sup_of_le_normalizer {N Y : Subgroup G} (hY : Y ≤ normalizer (N : Set G)) :
    N ≤ normalizer ((Y ⊔ N : Subgroup G) : Set G) := by
  intro n hn
  refine mem_normalizer_of_map_conj_le ?_
  rw [Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rintro _ ⟨y, hy, rfl⟩
    change n * y * n⁻¹ ∈ Y ⊔ N
    have h1 : y⁻¹ * n * y ∈ N := by
      have := (mem_normalizer_iff.mp (hY (Y.inv_mem hy)) n).mp hn
      simpa using this
    have : n * y * n⁻¹ = y * ((y⁻¹ * n * y) * n⁻¹) := by group
    rw [this]
    exact mul_mem_sup hy (N.mul_mem h1 (N.inv_mem hn))
  · rw [G4b.mem_normalizer_iff_map_conj_eq'.mp (le_normalizer hn)]
    exact le_sup_right

omit [Finite G] in
theorem mem_normalizer_sup {H K : Subgroup G} {g : G} (hH : g ∈ normalizer (H : Set G))
    (hK : g ∈ normalizer (K : Set G)) : g ∈ normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  rw [G4b.mem_normalizer_iff_map_conj_eq'] at hH hK ⊢
  rw [Subgroup.map_sup, hH, hK]

theorem odd_card_sup_of_le_normalizer {N Y : Subgroup G} (hY : Y ≤ normalizer (N : Set G))
    (hN : Odd (Nat.card N)) (hYo : Odd (Nat.card Y)) : Odd (Nat.card (N ⊔ Y : Subgroup G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(N ⊔ Y)) 2 h2
  have hx2 : (x : G) * x = 1 := by
    have h := pow_orderOf_eq_one x
    rw [hx, pow_two] at h
    exact congrArg Subtype.val h
  obtain ⟨n, hn, y, hy, hxy⟩ := mem_sup_of_le_normalizer hY x.2
  rw [← hxy] at hx2
  have hyN' : y * n * y⁻¹ ∈ N := (mem_normalizer_iff.mp (hY hy) n).mp hn
  have hy2 : y * y ∈ N := by
    have : y * y = (y * n * y⁻¹)⁻¹ * n⁻¹ * (n * y * (n * y)) := by group
    rw [this, hx2, mul_one]
    exact N.mul_mem (N.inv_mem hyN') (N.inv_mem hn)
  have hyodd : Odd (orderOf y) := hYo.of_dvd_nat (Subgroup.orderOf_dvd_natCard Y hy)
  obtain ⟨k, hk⟩ := hyodd
  have hyN : y ∈ N := by
    have h1 : y = (y * y) ^ (k + 1) := by
      rw [← pow_two, ← pow_mul, show 2 * (k + 1) = orderOf y + 1 by omega, pow_succ,
        pow_orderOf_eq_one, one_mul]
    rw [h1]
    exact N.pow_mem hy2 _
  have hxN : (x : G) ∈ N := hxy ▸ N.mul_mem hn hyN
  have hxo : orderOf (x : G) = 2 := by rw [Subgroup.orderOf_coe, hx]
  have hdvd : orderOf (x : G) ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hxN
  rw [hxo] at hdvd
  exact (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr hdvd)

omit [Finite G] in
theorem mem_of_mul_mem_of_isPGroup_two {N O : Subgroup G} (hON : O ≤ normalizer (N : Set G))
    (hO : Odd (Nat.card O)) {z o : G} (hz : z ∈ N) (ho : o ∈ O)
    (hy : IsPGroup 2 (zpowers (z * o))) : z * o ∈ N := by
  have hpow : ∀ m : ℕ, ∃ w ∈ N, (z * o) ^ m = w * o ^ m := by
    intro m
    induction m with
    | zero => exact ⟨1, N.one_mem, by simp⟩
    | succ m ih =>
      obtain ⟨w, hw, hwm⟩ := ih
      refine ⟨w * (o ^ m * z * (o ^ m)⁻¹), N.mul_mem hw ?_, ?_⟩
      · exact (mem_normalizer_iff.mp (hON (O.pow_mem ho m)) z).mp hz
      · rw [pow_succ, hwm, pow_succ]
        group
  obtain ⟨k, hk⟩ := hy ⟨z * o, mem_zpowers _⟩
  have hk' : (z * o) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  obtain ⟨w, hw, hwk⟩ := hpow (2 ^ k)
  have hok : o ^ 2 ^ k ∈ N := by
    have : o ^ 2 ^ k = w⁻¹ * (z * o) ^ 2 ^ k := by rw [hwk]; group
    rw [this, hk', mul_one]
    exact N.inv_mem hw
  have hodd : Odd (orderOf o) := hO.of_dvd_nat (Subgroup.orderOf_dvd_natCard O ho)
  have hcop : Nat.Coprime (2 ^ k) (orderOf o) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  have hoN : o ∈ N := by
    have hmem : o ∈ zpowers (o ^ 2 ^ k) := mem_zpowers_pow_iff.mpr hcop
    exact (zpowers_le.mpr hok) hmem
  exact N.mul_mem hz hoN

end Joins

section SylowQ

variable {G : Type*} [Group G] [Finite G]

theorem inf_O_centralizer_le {p : ℕ} [Fact p.Prime] {H₀ P X Q H₁ : Subgroup G}
    (hQdef : Q = P ⊓ O H₀) (hH₁def : H₁ = H₀ ⊓ normalizer (Q : Set G)) (hPH₀ : P ≤ H₀)
    (hQ : ABGLocalTools.IsSylowOf p Q (O H₀)) (hX2 : IsPGroup 2 X) (hXH₁ : X ≤ H₁)
    (hH₁X : ⁅H₁, X⁆ ≤ O H₁) : P ⊓ O (centralizer (X : Set G)) ≤ Q := by
  have hH₁H₀ : H₁ ≤ H₀ := hH₁def ▸ inf_le_left
  have hPH₁ : P ≤ H₁ := by
    rw [hH₁def]
    exact fun x hx => ⟨hPH₀ hx, hQdef ▸ inf_normalizer_le_normalizer_inf
      ⟨le_normalizer hx, le_normalizer_O H₀ (hPH₀ hx)⟩⟩
  have hOH₁ : O H₁ ≤ H₁ := map_subtype_le _
  have hOH₀ : O H₀ ≤ H₀ := map_subtype_le _
  have hFr : H₀ ≤ O H₀ ⊔ H₁ := by
    have h := eq_sup_inf_normalizer_of_isSylowOf hOH₀ (le_normalizer_O H₀) hQ
    rw [← hH₁def] at h
    exact h.le
  have hOH₁OH₀ : O H₁ ≤ normalizer (O H₀ : Set G) :=
    (hOH₁.trans hH₁H₀).trans (le_normalizer_O H₀)
  have hOO : O H₁ ≤ O H₀ := by
    have hle : O H₀ ⊔ O H₁ ≤ O H₀ := by
      refine le_O_of_le_normalizer (sup_le hOH₀ (hOH₁.trans hH₁H₀)) ?_
        (odd_card_sup_of_le_normalizer hOH₁OH₀ (card_O_odd H₀) (card_O_odd H₁))
      refine hFr.trans (sup_le ?_ ?_)
      · rw [sup_comm]
        exact le_normalizer_sup_of_le_normalizer hOH₁OH₀
      · exact fun h hh => mem_normalizer_sup (le_normalizer_O H₀ (hH₁H₀ hh))
          (le_normalizer_O H₁ hh)
    exact le_sup_right.trans hle
  have hdec : H₁ ≤ O H₁ ⊔ (H₁ ⊓ centralizer (X : Set G)) := by
    intro h hh
    have hstab : ∀ x ∈ X, x * h * x⁻¹ * h⁻¹ ∈ O H₁ := by
      intro x hx
      apply hH₁X
      rw [commutator_comm]
      exact commutator_mem_commutator hx hh
    obtain ⟨d, hd, hfix⟩ := exists_fixed_mem_coset_of_isPGroup hX2 (card_O_odd H₁)
      (hXH₁.trans (le_normalizer_O H₁)) hstab
    have hdh : d * h ∈ H₁ ⊓ centralizer (X : Set G) := by
      refine ⟨H₁.mul_mem (hOH₁ hd) hh, mem_centralizer_iff.mpr fun x hx => ?_⟩
      have := hfix x hx
      calc x * (d * h) = x * (d * h) * x⁻¹ * x := by group
        _ = d * h * x := by rw [this]
    have : h = d⁻¹ * (d * h) := by group
    rw [this]
    exact mul_mem_sup ((O H₁).inv_mem hd) hdh
  have hD₁N : O (centralizer (X : Set G)) ⊓ H₁ ≤ normalizer (O H₁ : Set G) :=
    inf_le_right.trans (le_normalizer_O H₁)
  have hD₁ : O (centralizer (X : Set G)) ⊓ H₁ ≤ O H₁ := by
    have hle : (O (centralizer (X : Set G)) ⊓ H₁) ⊔ O H₁ ≤ O H₁ := by
      refine le_O_of_le_normalizer (sup_le inf_le_right hOH₁) ?_ ?_
      · refine hdec.trans (sup_le (le_normalizer_sup_of_le_normalizer hD₁N) ?_)
        intro c hc
        exact mem_normalizer_sup (inf_normalizer_le_normalizer_inf
          ⟨le_normalizer_O _ hc.2, le_normalizer hc.1⟩) (le_normalizer_O H₁ hc.1)
      · rw [sup_comm]
        exact odd_card_sup_of_le_normalizer hD₁N (card_O_odd H₁)
          ((card_O_odd _).of_dvd_nat (card_dvd_of_le inf_le_left))
    exact le_sup_left.trans hle
  intro y ⟨hyP, hyO⟩
  rw [hQdef]
  exact ⟨hyP, hOO (hD₁ ⟨hyO, hPH₁ hyP⟩)⟩

end SylowQ

section Bar

theorem mem_of_commutator_mem_of_quotIs {G : Type} [Group G] {M₀ OM : Subgroup G} {qmin : ℕ}
    (hq : QuotIs M₀ OM (fun L _ => IsL2OrA7 L qmin)) {m : G} (hm : m ∈ M₀)
    (h : ∀ m' ∈ M₀, m * m' * m⁻¹ * m'⁻¹ ∈ OM) : m ∈ OM := by
  obtain ⟨L, _, f, hf, hker, hL⟩ := hq
  have hc : f ⟨m, hm⟩ ∈ center L := by
    rw [mem_center_iff]
    intro l
    obtain ⟨⟨m', hm'⟩, rfl⟩ := hf l
    have e : (⟨m, hm⟩ : M₀) * ⟨m', hm'⟩ * (⟨m, hm⟩ : M₀)⁻¹ * (⟨m', hm'⟩ : M₀)⁻¹ ∈ f.ker := by
      rw [hker]
      exact h m' hm'
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv,
      ← commutatorElement_def, commutatorElement_eq_one_iff_mul_comm] at e
    exact e.symm
  rw [CFSG.GH72.center_eq_bot_of_isL2OrA7 hL, mem_bot] at hc
  have h1 : (⟨m, hm⟩ : M₀) ∈ f.ker := hc
  rw [hker] at h1
  exact h1

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem le_sup_O_or_commutator_mem_O {H L₀ Z₀ : Subgroup G} (hL₀H : L₀ ≤ H) (hZ₀H : Z₀ ≤ H)
    (hHZ₀ : H ≤ normalizer (Z₀ : Set G)) (hL : ((L₀ ⊔ O H).subgroupOf H).Normal)
    (hs : IsSimpleGroup (bar H L₀)) :
    L₀ ≤ Z₀ ⊔ O H ∨ ∀ z ∈ Z₀, ∀ m ∈ L₀, z * m * z⁻¹ * m⁻¹ ∈ O H := by
  set π : H →* Bar H := QuotientGroup.mk' (CFSG.oddCore H) with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  set Zb : Subgroup (Bar H) := (Z₀.subgroupOf H).map π with hZb
  set Lb : Subgroup (Bar H) := bar H L₀ with hLb
  have hZbn : Zb.Normal :=
    ((normal_subgroupOf_iff_le_normalizer hZ₀H).mpr hHZ₀).map π hπ
  have hLbeq : Lb = ((L₀ ⊔ O H).subgroupOf H).map π := by
    rw [subgroupOf_sup hL₀H (map_subtype_le _), Subgroup.map_sup,
      show (O H).subgroupOf H = CFSG.oddCore H from
        comap_map_eq_self_of_injective H.subtype_injective _,
      show (CFSG.oddCore H).map π = ⊥ from QuotientGroup.map_mk'_self _, sup_bot_eq]
    rfl
  have hLbn : Lb.Normal := hLbeq ▸ hL.map π hπ
  have hInf : ((Zb ⊓ Lb).subgroupOf Lb).Normal :=
    (inferInstance : (Zb ⊓ Lb).Normal).subgroupOf Lb
  have := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Zb ⊓ Lb).subgroupOf Lb) with h | h
  ·
    right
    have hbot : Zb ⊓ Lb = ⊥ := by
      rw [← map_subgroupOf_eq_of_le (inf_le_right : Zb ⊓ Lb ≤ Lb), h, Subgroup.map_bot]
    intro z hz m hm
    have ha : π ⟨z, hZ₀H hz⟩ ∈ Zb := mem_map_of_mem _ (show (⟨z, hZ₀H hz⟩ : H) ∈ Z₀.subgroupOf H
      from hz)
    have hb : π ⟨m, hL₀H hm⟩ ∈ Lb := mem_map_of_mem _ (show (⟨m, hL₀H hm⟩ : H) ∈ L₀.subgroupOf H
      from hm)
    have hc : ⁅π ⟨z, hZ₀H hz⟩, π ⟨m, hL₀H hm⟩⁆ ∈ Zb ⊓ Lb := by
      refine ⟨?_, ?_⟩
      · rw [commutatorElement_def, mul_assoc, mul_assoc]
        exact Zb.mul_mem ha (by
          have := hZbn.conj_mem _ (Zb.inv_mem ha) (π ⟨m, hL₀H hm⟩)
          simpa [mul_assoc] using this)
      · rw [commutatorElement_def]
        exact Lb.mul_mem (hLbn.conj_mem _ hb _) (Lb.inv_mem hb)
    rw [hbot, mem_bot, ← map_commutatorElement, hπdef, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hc
    exact ⟨_, hc, rfl⟩
  ·
    left
    have hLZ : Lb ≤ Zb := by
      have h1 := (subgroupOf_eq_top (H := Zb ⊓ Lb) (K := Lb)).mp h
      exact h1.trans inf_le_left
    intro m hm
    obtain ⟨⟨z, hzH⟩, hz, hzm⟩ := hLZ (mem_map_of_mem _ (show (⟨m, hL₀H hm⟩ : H) ∈
      L₀.subgroupOf H from hm))
    rw [hπdef, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hzm
    have hzo : z⁻¹ * m ∈ O H := ⟨_, hzm, rfl⟩
    have : m = z * (z⁻¹ * m) := by group
    rw [this]
    exact mul_mem_sup hz hzo

end Bar

section PCore

variable {G : Type*} [Group G]

theorem normalizer_le_normalizer_pCore_map (p : ℕ) (K : Subgroup G) :
    normalizer (K : Set G) ≤
      normalizer (((CFSG.pCore p K).map K.subtype : Subgroup G) : Set G) := by
  intro s hs
  let phi : MulAut K := K.normalizerMonoidHom ⟨s, hs⟩
  have hhom : (MulAut.conj s).toMonoidHom.comp K.subtype = K.subtype.comp phi.toMonoidHom := by
    ext d
    rfl
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  change ((CFSG.pCore p K).map K.subtype).map (MulAut.conj s).toMonoidHom = _
  rw [Subgroup.map_map, hhom, ← Subgroup.map_map, CFSG.pCore_map_iso p phi]

end PCore

end G5d

end CFSG.GH72
