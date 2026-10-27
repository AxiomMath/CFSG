module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXHardDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXA5
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXFam
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXModel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.DX

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.T263

variable {p : ℕ}

section Impl

open scoped commutatorElement

variable {Ω : Type} [Group Ω]

private def Impl (S : Subgroup Ω) (b : Ω) (l : ↥S) : Prop :=
  ∀ y ∈ S, b⁻¹ * y * b = (l : Ω)⁻¹ * y * (l : Ω)

variable {S : Subgroup Ω}

private theorem Impl.one : Impl S 1 1 := fun y _ => by simp

private theorem Impl.mul {b₁ b₂ : Ω} {l₁ l₂ : ↥S} (h₁ : Impl S b₁ l₁) (h₂ : Impl S b₂ l₂) :
    Impl S (b₁ * b₂) (l₁ * l₂) := by
  intro y hy
  have h2 := h₂ ((l₁ : Ω)⁻¹ * y * (l₁ : Ω))
    (S.mul_mem (S.mul_mem (S.inv_mem l₁.2) hy) l₁.2)
  calc (b₁ * b₂)⁻¹ * y * (b₁ * b₂) = b₂⁻¹ * (b₁⁻¹ * y * b₁) * b₂ := by group
    _ = b₂⁻¹ * ((l₁ : Ω)⁻¹ * y * (l₁ : Ω)) * b₂ := by rw [h₁ y hy]
    _ = (l₂ : Ω)⁻¹ * ((l₁ : Ω)⁻¹ * y * (l₁ : Ω)) * (l₂ : Ω) := h2
    _ = ((l₁ * l₂ : ↥S) : Ω)⁻¹ * y * ((l₁ * l₂ : ↥S) : Ω) := by
      rw [Subgroup.coe_mul]
      group

private theorem Impl.conj_eq {b : Ω} {l : ↥S} (h : Impl S b l) {y : Ω} (hy : y ∈ S) :
    b * y * b⁻¹ = (l : Ω) * y * (l : Ω)⁻¹ := by
  have hz : (l : Ω) * y * (l : Ω)⁻¹ ∈ S := S.mul_mem (S.mul_mem l.2 hy) (S.inv_mem l.2)
  have h2 : b⁻¹ * ((l : Ω) * y * (l : Ω)⁻¹) * b = y := by
    rw [h _ hz]
    group
  calc b * y * b⁻¹ = b * (b⁻¹ * ((l : Ω) * y * (l : Ω)⁻¹) * b) * b⁻¹ := by rw [h2]
    _ = (l : Ω) * y * (l : Ω)⁻¹ := by group

private theorem Impl.inv {b : Ω} {l : ↥S} (h : Impl S b l) : Impl S b⁻¹ l⁻¹ := by
  intro y hy
  simp only [inv_inv, Subgroup.coe_inv]
  exact h.conj_eq hy

private theorem Impl.pow {b : Ω} {l : ↥S} (h : Impl S b l) (n : ℕ) :
    Impl S (b ^ n) (l ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    exact Impl.one
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact ih.mul h

private theorem Impl.mem_center {l : ↥S} (h : Impl S 1 l) : l ∈ Subgroup.center ↥S := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  have h1 := h g g.2
  have h2 : ((g : ↥S) : Ω) = (l : Ω)⁻¹ * g * (l : Ω) := by simpa using h1
  calc ((g * l : ↥S) : Ω) = (g : Ω) * (l : Ω) := rfl
    _ = (l : Ω) * ((l : Ω)⁻¹ * g * (l : Ω)) := by group
    _ = (l : Ω) * g := by rw [← h2]
    _ = ((l * g : ↥S) : Ω) := rfl

private theorem Impl.mul_inv_mem_center {b : Ω} {l l' : ↥S} (h : Impl S b l) (h' : Impl S b l') :
    l * l'⁻¹ ∈ Subgroup.center ↥S := by
  have h1 : Impl S (b * b⁻¹) (l * l'⁻¹) := h.mul h'.inv
  rw [mul_inv_cancel] at h1
  exact h1.mem_center

private theorem Impl.comm_eq {b : Ω} {l : ↥S} (h : Impl S b l) (t : ↥S) :
    ((⁅l, t⁆ : ↥S) : Ω) = ⁅b, (t : Ω)⁆ := by
  have := h.conj_eq t.2
  simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [← this]

private def implSub (S B₀ : Subgroup Ω) : Subgroup ↥S where
  carrier := {l | ∃ b ∈ B₀, Impl S b l}
  one_mem' := ⟨1, B₀.one_mem, Impl.one⟩
  mul_mem' := by
    rintro _ _ ⟨b₁, hb₁, h₁⟩ ⟨b₂, hb₂, h₂⟩
    exact ⟨b₁ * b₂, B₀.mul_mem hb₁ hb₂, h₁.mul h₂⟩
  inv_mem' := by
    rintro _ ⟨b, hb, h⟩
    exact ⟨b⁻¹, B₀.inv_mem hb, h.inv⟩

end Impl

section ImplFin

variable {Ω : Type} [Group Ω] [Finite Ω] {S B₀ : Subgroup Ω}

private theorem exists_impl (hSp : GLAPPrimeCore p ↥S = ⊥)
    (hin : ∀ b ∈ B₀, InducesInnerMod p S b) {b : Ω} (hb : b ∈ B₀) : ∃ l : ↥S, Impl S b l := by
  obtain ⟨l, hl, h⟩ := exists_conj_of_inducesInner hSp (hin b hb)
  exact ⟨⟨l, hl⟩, h⟩

open scoped commutatorElement in
private theorem commutator_implSub_eq {T' : Subgroup Ω} {x : Ω}
    (hSp : GLAPPrimeCore p ↥S = ⊥) (hin : ∀ b ∈ B₀, InducesInnerMod p S b) (hT'S : T' ≤ S) :
    (⁅implSub S B₀, (T' ⊓ Subgroup.centralizer ({x} : Set Ω)).subgroupOf S⁆ : Subgroup ↥S) =
      (⁅B₀, T' ⊓ Subgroup.centralizer ({x} : Set Ω)⁆ : Subgroup Ω).subgroupOf S := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    rintro l ⟨b, hb, hbl⟩ t ht
    show ((⁅l, t⁆ : ↥S) : Ω) ∈ ⁅B₀, T' ⊓ Subgroup.centralizer ({x} : Set Ω)⁆
    rw [hbl.comm_eq t]
    exact Subgroup.commutator_mem_commutator hb ht
  · intro s hs
    have hle : (⁅B₀, T' ⊓ Subgroup.centralizer ({x} : Set Ω)⁆ : Subgroup Ω) ≤
        (⁅implSub S B₀, (T' ⊓ Subgroup.centralizer ({x} : Set Ω)).subgroupOf S⁆ :
          Subgroup ↥S).map S.subtype := by
      rw [Subgroup.commutator_le]
      intro b hb t ht
      obtain ⟨l, hl⟩ := exists_impl hSp hin hb
      have htS : t ∈ S := hT'S ht.1
      exact ⟨⁅l, ⟨t, htS⟩⁆, Subgroup.commutator_mem_commutator ⟨b, hb, hl⟩ ht,
        hl.comm_eq ⟨t, htS⟩⟩
    obtain ⟨m, hm, hms⟩ := hle hs
    have hms' : m = s := Subtype.ext hms
    rwa [← hms']

end ImplFin

variable {Ω : Type} [Group Ω] [Finite Ω]


theorem selComp_or_a5_of_modelSelH (hp : p.Prime) (hp2 : p ≠ 2) {S B₀ T' : Subgroup Ω} {x : Ω}
    (hSn : S.Normal) (hSq : CFSG.Open.IsQuasisimple ↥S) (hSp : GLAPPrimeCore p ↥S = ⊥)
    (hSc : IsChevSimple 2 (↥S ⧸ Subgroup.center ↥S))
    (hF2 : p = 3 → ¬ GLAMarking (↥S) (fun lab _ _ _ _ _ => lab.n = 1))
    (hB₀p : ∀ b ∈ B₀, b ^ p = 1) (hB₀c : ∀ a ∈ B₀, ∀ b ∈ B₀, a * b = b * a) (hxB₀ : x ∈ B₀)
    (hxC : x ∉ Subgroup.centralizer (S : Set Ω)) (hInn : InnDiagOn p B₀ S)
    (hin : ∀ b ∈ B₀, InducesInnerMod p S b) (hT'2 : IsPGroup 2 ↥T') (hT'S : T' ≤ S)
    (hB₀T' : B₀ ≤ Subgroup.normalizer (T' : Set Ω))
    (hS₁ : (⁅B₀, T' ⊓ Subgroup.centralizer ({x} : Set Ω)⁆ : Subgroup Ω) ≠ ⊥)
    {T : Type} [Group T] [Finite T] (e : ↥S ⧸ Subgroup.center ↥S ≃* T) (hT : ModelSelH p T) :
    ∃ J : Subgroup Ω, SelComp p S B₀ T' x J ∨
      (p = 3 ∧ IsComponentOf J (S ⊓ Subgroup.centralizer ({x} : Set Ω)) ∧
        Nat.card (↥J ⧸ Subgroup.center ↥J) = 60) := by
  have hxp : x ^ p = 1 := hB₀p x hxB₀
  obtain ⟨l₀, hconj, hl₀p, hl₀nc⟩ := exists_conj_element hSp (hin x hxB₀) hxp hxC
  set S₁ : Subgroup Ω := ⁅B₀, T' ⊓ Subgroup.centralizer ({x} : Set Ω)⁆ with hS₁def
  have hconjTC : ∀ b ∈ B₀, ∀ t ∈ T' ⊓ Subgroup.centralizer ({x} : Set Ω),
      b * t * b⁻¹ ∈ T' ⊓ Subgroup.centralizer ({x} : Set Ω) := by
    intro b hb t ht
    refine ⟨(Subgroup.mem_normalizer_iff.1 (hB₀T' hb) t).1 ht.1, ?_⟩
    have hbx : Commute b x := hB₀c b hb x hxB₀
    have htx : Commute t x := Subgroup.mem_centralizer_singleton_iff.1 ht.2
    exact Subgroup.mem_centralizer_singleton_iff.2 ((hbx.mul_left htx).mul_left hbx.inv_left).eq
  have hS₁T : S₁ ≤ T' ⊓ Subgroup.centralizer ({x} : Set Ω) := by
    rw [hS₁def, Subgroup.commutator_le]
    intro b hb t ht
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (hconjTC b hb t ht) (Subgroup.inv_mem _ ht)
  have hS₁S : S₁ ≤ S ⊓ Subgroup.centralizer ({x} : Set Ω) :=
    fun s hs => ⟨hT'S (hS₁T hs).1, (hS₁T hs).2⟩
  have hS₁2 : IsPGroup 2 ↥S₁ := hT'2.to_le (hS₁T.trans inf_le_left)
  let σ : ↥S →* T := centerQuotHom e
  have hσk : ∀ s : ↥S, σ s = 1 ↔ s ∈ Subgroup.center ↥S := centerQuotHom_eq_one_iff e
  let L : Subgroup ↥S := implSub S B₀
  let X : Subgroup ↥S := (T' ⊓ Subgroup.centralizer ({x} : Set Ω)).subgroupOf S
  have hrp : (σ l₀) ^ p = 1 := by
    rw [← map_pow]
    exact (hσk _).2 hl₀p
  have hr1 : σ l₀ ≠ 1 := fun h => hl₀nc ((hσk l₀).1 h)
  have hl₀L : l₀ ∈ L := ⟨x, hxB₀, hconj⟩
  have hAp : ∀ a ∈ L.map σ, a ^ p = 1 := by
    rintro _ ⟨l, ⟨b, hb, hbl⟩, rfl⟩
    have h1 : Impl S (b ^ p) (l ^ p) := hbl.pow p
    rw [hB₀p b hb] at h1
    rw [← map_pow]
    exact (hσk _).2 h1.mem_center
  have hAc : ∀ a ∈ L.map σ, ∀ a' ∈ L.map σ, a * a' = a' * a := by
    rintro _ ⟨l₁, ⟨b₁, hb₁, h₁⟩, rfl⟩ _ ⟨l₂, ⟨b₂, hb₂, h₂⟩, rfl⟩
    have h12 : Impl S (b₁ * b₂) (l₁ * l₂) := h₁.mul h₂
    have h21 : Impl S (b₁ * b₂) (l₂ * l₁) := by
      have := h₂.mul h₁
      rwa [hB₀c b₂ hb₂ b₁ hb₁] at this
    have h0 : σ (l₁ * l₂ * (l₂ * l₁)⁻¹) = 1 := (hσk _).2 (h12.mul_inv_mem_center h21)
    rw [map_mul, map_inv, mul_inv_eq_one, map_mul, map_mul] at h0
    exact h0
  have hQC : X.map σ ≤ Subgroup.centralizer ({σ l₀} : Set T) := by
    rintro _ ⟨s, hs, rfl⟩
    have hsx : (s : Ω) * x = x * s := Subgroup.mem_centralizer_singleton_iff.1 hs.2
    have hsl : (s : Ω) * l₀ = l₀ * s := (commute_x_iff_commute_l_of_conj hconj s.2).1 hsx
    rw [Subgroup.mem_centralizer_singleton_iff]
    change σ s * σ l₀ = σ l₀ * σ s
    rw [← map_mul, ← map_mul]
    exact congrArg σ (Subtype.ext hsl)
  have hX2 : IsPGroup 2 ↥X := hT'2.to_inf_left.comap_subtype
  have hQ2 : IsPGroup 2 ↥(X.map σ) := hX2.map σ
  have hAQ : L.map σ ≤ Subgroup.normalizer ((X.map σ : Subgroup T) : Set T) := by
    rw [Subgroup.le_normalizer_iff]
    rintro _ ⟨l, ⟨b, hb, hbl⟩, rfl⟩ _ ⟨t, ht, rfl⟩
    have hmem : l * t * l⁻¹ ∈ X := by
      show ((l * t * l⁻¹ : ↥S) : Ω) ∈ T' ⊓ Subgroup.centralizer ({x} : Set Ω)
      have h1 : ((l * t * l⁻¹ : ↥S) : Ω) = b * (t : Ω) * b⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        exact (hbl.conj_eq t.2).symm
      rw [h1]
      exact hconjTC b hb t ht
    have h2 := Subgroup.mem_map_of_mem σ hmem
    rw [map_mul, map_mul, map_inv] at h2
    exact h2
  have hLX : (⁅L, X⁆ : Subgroup ↥S) = S₁.subgroupOf S :=
    commutator_implSub_eq hSp hin hT'S
  have hAQeq : (⁅L.map σ, X.map σ⁆ : Subgroup T) = (S₁.subgroupOf S).map σ := by
    rw [← hLX, Subgroup.map_commutator]
  have hAQne : (⁅L.map σ, X.map σ⁆ : Subgroup T) ≠ ⊥ := by
    rw [hAQeq]
    exact map_centerQuotHom_ne_bot hp hp2 hSp hS₁ (hS₁S.trans inf_le_left) hS₁2 e
  obtain ⟨JT, hJTc, hJTp, hJTa, hJTP⟩ := hT (σ l₀) hrp hr1 (L.map σ) (X.map σ)
    (Subgroup.mem_map_of_mem σ hl₀L) hAp hAc hQC hQ2 hAQ hAQne
  obtain ⟨J, hJ⟩ := selCompCore_of_component hp hp2 hSq hSc hconj hl₀p hl₀nc hS₁S e hAQeq hJTc
    hJTp hJTa hJTP
  exact ⟨J, selComp_or_a5_of_core hp hp2 hSn hSq hSp hF2 hxp hxC
    (S10.innDiagOn_mono hInn (Subgroup.zpowers_le.2 hxB₀)) (hin x hxB₀) hJ⟩

theorem t263SelWP_of_modelH {Q : ℕ → TauCeti.CFSGIndex → Prop}
    (hmod : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ (X : Type) [Group X], catalogIs X (Q p) →
      ∃ (T : Type) (_ : Group T) (_ : Finite T), Nonempty (X ≃* T) ∧ ModelSelH p T)
    (hinn : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ (Ω : Type) [Group Ω] [Finite Ω] (S : Subgroup Ω)
      (x : Ω), S.Normal → CFSG.Open.IsQuasisimple ↥S → GLAPPrimeCore p ↥S = ⊥ →
      catalogIs (↥S ⧸ Subgroup.center ↥S) (Q p) → x ^ p = 1 →
      InnDiagOn p (Subgroup.zpowers x) S → InducesInnerMod p S x) :
    T263SelWP Q := by
  intro p hp hp2 Ω _ _ hK S B hSn hSq hSp hSc hcat hF2 hSB hΩ hB h4 hT hC B₀ hB₀ hdich hcase T'
    hT'ne hT'2 hT'S hBT' hker x hxB₀ hxC hxcomm
  obtain ⟨hBel, hBcard, -⟩ : IsElemAbelian p B ∧ Nat.card ↥B = p ^ GLATwoLocalRank p Ω ∧
      ∃ U : Subgroup Ω, U ≠ ⊥ ∧ IsPGroup 2 U ∧ B ≤ Subgroup.normalizer (U : Set Ω) := id hB
  have hB₀B : B₀ ≤ B := hB₀.1
  have hxB : x ∈ B := hB₀B hxB₀
  obtain ⟨T, _, _, ⟨e⟩, hTsel⟩ := hmod p hp hp2 _ hcat
  have hin : ∀ b ∈ B₀, InducesInnerMod p S b := fun b hb =>
    hinn p hp hp2 Ω S b hSn hSq hSp hcat (hBel.2 b (hB₀B hb))
      (S10.innDiagOn_mono hB₀.2.1 (Subgroup.zpowers_le.2 hb))
  obtain ⟨J, hJ | ⟨hp3, hJc, h60⟩⟩ := selComp_or_a5_of_modelSelH hp hp2 hSn hSq hSp hSc hF2
    (fun b hb => hBel.2 b (hB₀B hb))
    (fun a ha b hb => isElemAbelian_commute hBel (hB₀B ha) (hB₀B hb)) hxB₀ hxC hB₀.2.1 hin
    hT'2 hT'S (hB₀B.trans hBT') hxcomm e hTsel
  · exact Or.inr ⟨J, hJ⟩
  · subst hp3
    refine Or.inl (t263GConcl_of_a5 hSn hBel ?_ hxB hJc h60)
    rw [hBcard]
    exact Nat.pow_le_pow_right (by norm_num) h4

end CFSG.LocalAnalysis.GLTheoremA.T263.DX
