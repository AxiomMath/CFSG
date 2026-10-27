module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6S

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.A6h1

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S
open CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Q3.TC.Thin

abbrev ae6AE8 : Subgroup (AE.AEQ 8) := (AE.aeSub 8).map (AE.mkQ 8)

@[expose] noncomputable def ae6ParM (a b : AE.AEQ 8) : Subgroup (AE.AEQ 8) :=
  ⨆ (δ : Finset (Fin 8)) (h : δ.card = 4) (c : Bool)
    (_ : AE.zBar δ h = a ∨ AE.zBar δ h = b ∨ AE.zBar δ h = a * b), AE.memBar δ h c

structure AE6ParFacts (𝔐 : Subgroup (AE.AEQ 8)) : Prop where
  card : Nat.card 𝔐 = 12288
  overg : ∀ X : Subgroup (AE.AEQ 8), 𝔐 ≤ X → X ≤ ae6AE8 →
    X = 𝔐 ∨ X = ae6AE8 ∨ Nat.card X = 86016
  orbit : ∀ X : Subgroup (AE.AEQ 8), 𝔐 ≤ X → X ≤ ae6AE8 → Nat.card X = 86016 →
    ∀ (δ δ' : Finset (Fin 8)) (h : δ.card = 4) (h' : δ'.card = 4) (c c' : Bool),
      AE.memBar δ h c ≤ X → AE.memBar δ' h' c' ≤ X →
        ∃ e ∈ X, conjSub e (AE.memBar δ h c) = AE.memBar δ' h' c'

@[expose] def AE6ModelPar : Prop :=
  ∀ (α β γ : Finset (Fin 8)) (hα : α.card = 4) (hβ : β.card = 4) (hγ : γ.card = 4),
    AE.zBar α hα * AE.zBar β hβ = AE.zBar γ hγ →
      AE6ParFacts (ae6ParM (AE.zBar α hα) (AE.zBar β hβ))

theorem e29Sub_le : AE.e29Sub ≤ ae6AE8 :=
  Subgroup.map_mono inf_le_left

@[expose] def ae6Cyc : Equiv.Perm (Fin 8) := Equiv.swap 0 1 * Equiv.swap 1 2

theorem ae6Cyc_not_mem : ae6Cyc ∉ AE.agl32 := by
  intro h
  have h1 := (h {0, 2, 4, 6} (by decide)).1
  revert h1
  decide +kernel

theorem e29Sub_ne : AE.e29Sub ≠ ae6AE8 := by
  intro h
  have hmem : AE.mkQ 8 ⟨0, ae6Cyc⟩ ∈ ae6AE8 := by
    refine ⟨⟨0, ae6Cyc⟩, ⟨?_, ?_⟩, rfl⟩
    · simp [AE.Wr.wsum]
    · decide
  rw [← h] at hmem
  obtain ⟨a, ha, he⟩ := hmem
  have hp : a.perm = ae6Cyc := by
    rcases AE.mkQ_eq_iff.mp he with h1 | h1
    · rw [inv_mul_eq_one.mp h1]
    · have h2 := congrArg AE.Wr.perm h1
      rw [AE.Wr.mul_perm, AE.Wr.inv_perm] at h2
      have h3 : a.perm⁻¹ * ae6Cyc = 1 := h2
      exact inv_mul_eq_one.mp h3
  exact ae6Cyc_not_mem (hp ▸ ha.2)

@[expose] def ae6EvenVecEquiv : {v : Fin 8 → ZMod 2 // ∑ i, v i = 0} ≃ (Fin 7 → ZMod 2) where
  toFun v := Fin.init v.1
  invFun w := ⟨Fin.snoc w (-∑ i, w i), by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    ring⟩
  left_inv v := by
    obtain ⟨v, hv⟩ := v
    apply Subtype.ext
    have hl : -∑ i, Fin.init v i = v (Fin.last 7) := by
      rw [Fin.sum_univ_castSucc] at hv
      simp only [Fin.init]
      linear_combination -hv
    simp only
    rw [hl, Fin.snoc_init_self]
  right_inv w := Fin.init_snoc _ _

@[expose] def ae6AeSubEquiv :
    ↥(AE.aeSub 8) ≃ {v : Fin 8 → ZMod 2 // ∑ i, v i = 0} × ↥(alternatingGroup (Fin 8)) where
  toFun a := (⟨a.1.vec, (AE.mem_aeSub.mp a.2).1⟩,
    ⟨a.1.perm, Equiv.Perm.mem_alternatingGroup.mpr (AE.mem_aeSub.mp a.2).2⟩)
  invFun p := ⟨⟨p.1.1, p.2.1⟩, AE.mem_aeSub.mpr ⟨p.1.2, Equiv.Perm.mem_alternatingGroup.mp p.2.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_aeSub8 : Nat.card (AE.aeSub 8) = 2580480 := by
  rw [Nat.card_congr ae6AeSubEquiv, Nat.card_prod, Nat.card_congr ae6EvenVecEquiv, Nat.card_fun,
    Nat.card_zmod, Nat.card_fin, nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem allOnes_mem_aeSub8 : AE.Wr.allOnes 8 ∈ AE.aeSub 8 :=
  AE.mem_aeSub.mpr ⟨by decide, by decide⟩

theorem card_piSub8 : Nat.card (AE.piSub 8) = 2 := by
  have h : ((AE.piSub 8 : Subgroup (AE.Wr 8)) : Set (AE.Wr 8)) = {1, AE.Wr.allOnes 8} := by
    ext a
    simp only [SetLike.mem_coe, AE.mem_piSub, Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, h, Set.ncard_pair (by decide)]

theorem card_ae6AE8 : Nat.card ae6AE8 = 1290240 := by
  have h1 := Subgroup.relIndex_mul_card (AE.mkQ 8).ker (AE.aeSub 8)
  have hle : AE.piSub 8 ≤ AE.aeSub 8 := by
    intro a ha
    rcases AE.mem_piSub.mp ha with rfl | rfl
    · exact (AE.aeSub 8).one_mem
    · exact allOnes_mem_aeSub8
  rw [Subgroup.relIndex_ker, QuotientGroup.ker_mk', inf_eq_left.mpr hle, card_piSub8,
    card_aeSub8] at h1
  show Nat.card ((AE.aeSub 8).map (AE.mkQ 8)) = 1290240
  omega

theorem not_sup_eq_of_isPGroup {G : Type*} [Group G] [Finite G] {V E Q : Subgroup G}
    (hEV : E ≤ V) (hQV : Q ≤ V) (hQN : V ≤ Subgroup.normalizer (Q : Set G)) (hQ : IsPGroup 2 ↥Q)
    (hcard : Nat.card V = 15 * Nat.card E) : E ⊔ Q ≠ V := by
  intro hsup
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLE : E ≤ Subgroup.normalizer (Q : Set G) := hEV.trans hQN
  haveI := Subgroup.normal_subgroupOf_of_le_normalizer hLE
  haveI := Subgroup.normal_subgroupOf_sup_of_le_normalizer hLE
  have he : Q.relIndex E = Q.relIndex (E ⊔ Q) :=
    Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient E Q hLE).toEquiv
  rw [hsup] at he
  have h1 := Subgroup.relIndex_mul_card Q E
  have h2 := Subgroup.relIndex_mul_card Q V
  rw [inf_eq_left.mpr hQV, ← he] at h2
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  have h3 : Nat.card ↥Q = 15 * Nat.card ↥(Q ⊓ E) := by
    have hr : 0 < Q.relIndex E := by
      rcases Nat.eq_zero_or_pos (Q.relIndex E) with h0 | h0
      · rw [h0, zero_mul] at h2
        exact absurd h2.symm Nat.card_pos.ne'
      · exact h0
    apply Nat.eq_of_mul_eq_mul_left hr
    rw [h2, hcard, ← h1]
    ring
  have h4 : 3 ∣ 2 ^ k := hk ▸ h3 ▸ Dvd.dvd.mul_right (by norm_num : 3 ∣ 15) _
  have h5 := (Nat.prime_three.dvd_of_dvd_pow h4)
  omega

section Transport

variable {Y : Type} [Group Y] {V : Subgroup Y}

@[expose] def ae6Img (φ : ↥V →* AE.AEQ 8) (X : Subgroup Y) : Subgroup (AE.AEQ 8) :=
  (X.subgroupOf V).map φ

variable {φ : ↥V →* AE.AEQ 8}

theorem mem_ae6Img {X : Subgroup Y} {e : AE.AEQ 8} :
    e ∈ ae6Img φ X ↔ ∃ (g : Y) (hg : g ∈ V), g ∈ X ∧ φ ⟨g, hg⟩ = e := by
  constructor
  · rintro ⟨⟨g, hg⟩, hgX, rfl⟩
    exact ⟨g, hg, hgX, rfl⟩
  · rintro ⟨g, hg, hgX, rfl⟩
    exact ⟨⟨g, hg⟩, hgX, rfl⟩

theorem ae6Img_mono {X X' : Subgroup Y} (h : X ≤ X') : ae6Img φ X ≤ ae6Img φ X' :=
  Subgroup.map_mono fun _ hx => h hx

theorem ae6Img_le_iff (hφ : Function.Injective φ) {X X' : Subgroup Y} (hX : X ≤ V) :
    ae6Img φ X ≤ ae6Img φ X' ↔ X ≤ X' := by
  refine ⟨fun h x hx => ?_, ae6Img_mono⟩
  obtain ⟨g, hg, hgX', he⟩ := mem_ae6Img.mp (h (mem_ae6Img.mpr ⟨x, hX hx, hx, rfl⟩))
  have : g = x := congrArg Subtype.val (hφ he)
  exact this ▸ hgX'

theorem ae6Img_inj (hφ : Function.Injective φ) {X X' : Subgroup Y} (hX : X ≤ V) (hX' : X' ≤ V)
    (h : ae6Img φ X = ae6Img φ X') : X = X' :=
  le_antisymm ((ae6Img_le_iff hφ hX).mp h.le) ((ae6Img_le_iff hφ hX').mp h.ge)

theorem card_ae6Img (hφ : Function.Injective φ) {X : Subgroup Y} (hX : X ≤ V) :
    Nat.card (ae6Img φ X) = Nat.card X := by
  rw [ae6Img, Subgroup.card_map_of_injective hφ]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv

theorem ae6Img_self : ae6Img φ V = φ.range := by
  rw [ae6Img, Subgroup.subgroupOf_self, MonoidHom.range_eq_map]

theorem ae6Img_le_range (X : Subgroup Y) : ae6Img φ X ≤ φ.range :=
  Subgroup.map_le_range φ _

theorem ae6Img_conjSub {g : Y} (hg : g ∈ V) {J : Subgroup Y} (hJ : J ≤ V) :
    ae6Img φ (conjSub g J) = conjSub (φ ⟨g, hg⟩) (ae6Img φ J) := by
  ext e
  rw [mem_ae6Img, mem_conjSub_iff, mem_ae6Img]
  constructor
  · rintro ⟨x, hx, hxJ, rfl⟩
    rw [mem_conjSub_iff] at hxJ
    refine ⟨g⁻¹ * x * g, hJ hxJ, hxJ, ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  · rintro ⟨j, hj, hjJ, he⟩
    have hgj : g * j * g⁻¹ ∈ V := V.mul_mem (V.mul_mem hg hj) (V.inv_mem hg)
    refine ⟨g * j * g⁻¹, hgj, conj_mem_conjSub hjJ, ?_⟩
    have h1 : φ ⟨g * j * g⁻¹, hgj⟩ = φ ⟨g, hg⟩ * φ ⟨j, hj⟩ * (φ ⟨g, hg⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [h1, he]
    group

theorem conjSub_le_of_mem {G : Type*} [Group G] {X J : Subgroup G} {g : G} (hg : g ∈ X)
    (hJ : J ≤ X) : conjSub g J ≤ X :=
  (conjSub_mono hJ).trans (conjSub_eq_self_of_mem hg).le

theorem ae6Img_le_of_forall {S : Set (Subgroup Y)} (hS : ∀ J ∈ S, J ≤ V) {𝔛 : Subgroup (AE.AEQ 8)}
    (h : ∀ J ∈ S, ae6Img φ J ≤ 𝔛) : ae6Img φ (⨆ J ∈ S, J) ≤ 𝔛 := by
  have hJ : ∀ J ∈ S, J ≤ (𝔛.comap φ).map V.subtype := by
    intro J hJS x hx
    have hxV := hS J hJS hx
    have hx' : φ ⟨x, hxV⟩ ∈ 𝔛 := h J hJS (mem_ae6Img.mpr ⟨x, hxV, hx, rfl⟩)
    exact ⟨⟨x, hxV⟩, hx', rfl⟩
  refine (ae6Img_mono (iSup₂_le hJ)).trans ?_
  rintro _ ⟨⟨g, hg⟩, ⟨⟨g', hg'⟩, hg'𝔛, hgg'⟩, rfl⟩
  have : (⟨g', hg'⟩ : ↥V) = ⟨g, hg⟩ := Subtype.ext hgg'
  rw [← this]
  exact hg'𝔛

structure AE6Vertex (V M₀ : Subgroup Y) (P : Set (Subgroup Y)) : Prop where
  iso : Nat.card V = Nat.card ae6AE8
  le : M₀ ≤ V
  card : Nat.card M₀ = 12288
  overg : ∀ X : Subgroup Y, M₀ ≤ X → X ≤ V → X = M₀ ∨ X = V ∨ Nat.card X = 86016
  orbit : ∀ X : Subgroup Y, M₀ ≤ X → X ≤ V → Nat.card X = 86016 → ∀ J ∈ P, ∀ J' ∈ P, J ≤ X →
    J' ≤ X → ∃ g ∈ X, conjSub g J = J'

theorem ae6Vertex_of_img [Finite Y] (hφ : Function.Injective φ) (hrange : φ.range = ae6AE8)
    {M₀ : Subgroup Y} (hM₀ : M₀ ≤ V) {𝔐 : Subgroup (AE.AEQ 8)} (himg : ae6Img φ M₀ = 𝔐)
    (hF : AE6ParFacts 𝔐) {P : Set (Subgroup Y)}
    (hP : ∀ J ∈ P, J ≤ V ∧ ∃ (δ : Finset (Fin 8)) (h : δ.card = 4) (c : Bool),
      ae6Img φ J = AE.memBar δ h c) :
    AE6Vertex V M₀ P := by
  have hV : ae6Img φ V = ae6AE8 := ae6Img_self.trans hrange
  have hle : ∀ X : Subgroup Y, ae6Img φ X ≤ ae6AE8 := fun X => hrange ▸ ae6Img_le_range X
  refine ⟨?_, hM₀, ?_, ?_, ?_⟩
  · rw [← hV, card_ae6Img hφ le_rfl]
  · rw [← card_ae6Img hφ hM₀, himg, hF.card]
  · intro X hMX hXV
    rcases hF.overg (ae6Img φ X) (himg ▸ ae6Img_mono hMX) (hle X) with h | h | h
    · exact Or.inl (ae6Img_inj hφ hXV hM₀ (h.trans himg.symm))
    · exact Or.inr (Or.inl (ae6Img_inj hφ hXV le_rfl (h.trans hV.symm)))
    · exact Or.inr (Or.inr ((card_ae6Img hφ hXV).symm.trans h))
  · intro X hMX hXV hX J hJ J' hJ' hJX hJ'X
    obtain ⟨hJV, δ, h, c, hl⟩ := hP J hJ
    obtain ⟨hJ'V, δ', h', c', hl'⟩ := hP J' hJ'
    obtain ⟨e, he, hconj⟩ := hF.orbit (ae6Img φ X) (himg ▸ ae6Img_mono hMX) (hle X)
      ((card_ae6Img hφ hXV).trans hX) δ δ' h h' c c' (hl ▸ ae6Img_mono hJX)
      (hl' ▸ ae6Img_mono hJ'X)
    obtain ⟨g, hg, hgX, rfl⟩ := mem_ae6Img.mp he
    refine ⟨g, hgX, ae6Img_inj hφ (conjSub_le_of_mem hg hJV) hJ'V ?_⟩
    rw [ae6Img_conjSub hg hJV, hl, hl', hconj]

namespace AE6Vertex

variable {V M₀ : Subgroup Y} {P : Set (Subgroup Y)}

theorem inf [Finite Y] (v : AE6Vertex V M₀ P) {X X' : Subgroup Y} (hMX : M₀ ≤ X) (hMX' : M₀ ≤ X')
    (hXV : X ≤ V) (hX : Nat.card X = 86016) (hX' : Nat.card X' = 86016) (hne : X ≠ X') :
    X ⊓ X' = M₀ := by
  rcases v.overg (X ⊓ X') (le_inf hMX hMX') (inf_le_left.trans hXV) with h | h | h
  · exact h
  · have hVX : V ≤ X := by rw [← h]; exact inf_le_left
    have hVX' : V ≤ X' := by rw [← h]; exact inf_le_right
    have hXeq : X = V := le_antisymm hXV hVX
    have hX'eq : V = X' := Subgroup.eq_of_le_of_card_ge hVX' (by rw [hX', ← hX, hXeq])
    exact (hne (hXeq.trans hX'eq)).elim
  · have h1 : X ⊓ X' = X := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hX])
    have h2 : X ⊓ X' = X' := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, hX'])
    exact (hne (h1.symm.trans h2)).elim

theorem le_edge [Finite Y] (v : AE6Vertex V M₀ P) {E Q : Subgroup Y} (hME : M₀ ≤ E) (hEV : E ≤ V)
    (hE : Nat.card E = 86016) (hQV : Q ≤ V) (hQ : IsPGroup 2 ↥Q)
    (hQN : V ≤ Subgroup.normalizer (Q : Set Y)) : Q ≤ E := by
  rcases v.overg (E ⊔ Q) (hME.trans le_sup_left) (sup_le hEV hQV) with h | h | h
  · have h1 := Subgroup.card_le_of_le (le_sup_left.trans h.le : E ≤ M₀)
    rw [hE, v.card] at h1
    norm_num at h1
  · exact (not_sup_eq_of_isPGroup hEV hQV hQN hQ (by rw [v.iso, card_ae6AE8, hE]) h).elim
  · have h1 : E = E ⊔ Q := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h, hE])
    exact h1 ▸ le_sup_right

theorem pCoreOf_le [Finite Y] (v : AE6Vertex V M₀ P) {E : Subgroup Y} (hME : M₀ ≤ E)
    (hEV : E ≤ V) (hE : Nat.card E = 86016) : pCoreOf 2 V ≤ E := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact v.le_edge hME hEV hE (LieType.BorelTits.pCoreOf_le 2 V)
    (LieType.BorelTits.pCoreOf_isPGroup 2 V) (LieType.BorelTits.le_normalizer_pCoreOf 2 V)

end AE6Vertex

end Transport

section Vertex

variable {Y : Type} [Group Y] [Finite Y]

@[expose] def ae6M₀ (P : Set (Subgroup Y)) (t τ : Y) : Subgroup Y :=
  ⨆ J ∈ {J : Subgroup Y | J ∈ P ∧ (IsUniqueInvolution J t ∨ IsUniqueInvolution J τ ∨
    IsUniqueInvolution J (t * τ))}, J

theorem ae6Vertex_of_ident (hModel : AE6ModelPar) {P : Set (Subgroup Y)} (A : AEIdent P 8)
    (hker : A.φ.ker = ⊥) (h8 : ∀ J ∈ P, Nat.card J = 8)
    (hz : ∀ J ∈ P, ∃ z, IsUniqueInvolution J z) {t τ : Y} {J₁ J₂ J₃ : Subgroup Y}
    (h₁ : J₁ ∈ P) (h₂ : J₂ ∈ P) (h₃ : J₃ ∈ P) (ht₁ : IsUniqueInvolution J₁ t)
    (ht₂ : IsUniqueInvolution J₂ τ) (ht₃ : IsUniqueInvolution J₃ (t * τ)) :
    AE6Vertex (pSpan P) (ae6M₀ P t τ) P := by
  have hφ : Function.Injective A.φ := (MonoidHom.ker_eq_bot_iff _).mp hker
  have hn : 5 ≤ 8 := by norm_num
  obtain ⟨α, hα, c₁, hl₁⟩ := A.label J₁ h₁
  obtain ⟨β, hβ, c₂, hl₂⟩ := A.label J₂ h₂
  obtain ⟨γ, hγ, c₃, hl₃⟩ := A.label J₃ h₃
  have e₁ := phi_map_eq_zBar A.φ hn h₁ (h8 _ h₁) hl₁ ht₁
  have e₂ := phi_map_eq_zBar A.φ hn h₂ (h8 _ h₂) hl₂ ht₂
  have e₃ := phi_map_eq_zBar A.φ hn h₃ (h8 _ h₃) hl₃ ht₃
  have hprod : AE.zBar α hα * AE.zBar β hβ = AE.zBar γ hγ := by
    rw [← e₁, ← e₂, ← e₃, ← map_mul]
    rfl
  have hS : ∀ J ∈ {J : Subgroup Y | J ∈ P ∧ (IsUniqueInvolution J t ∨ IsUniqueInvolution J τ ∨
      IsUniqueInvolution J (t * τ))}, J ≤ pSpan P := fun J hJ => le_pSpan hJ.1
  have himg : ae6Img A.φ (ae6M₀ P t τ) = ae6ParM (AE.zBar α hα) (AE.zBar β hβ) := by
    apply le_antisymm
    · refine ae6Img_le_of_forall hS ?_
      rintro J ⟨hJ, hJt⟩
      obtain ⟨δ, hδ, c, hl⟩ := A.label J hJ
      have hl' : ae6Img A.φ J = AE.memBar δ hδ c := hl
      rw [hl']
      have hcond : AE.zBar δ hδ = AE.zBar α hα ∨ AE.zBar δ hδ = AE.zBar β hβ ∨
          AE.zBar δ hδ = AE.zBar α hα * AE.zBar β hβ := by
        rcases hJt with h | h | h
        · exact Or.inl ((phi_map_eq_zBar A.φ hn hJ (h8 _ hJ) hl h).symm.trans e₁)
        · exact Or.inr (Or.inl ((phi_map_eq_zBar A.φ hn hJ (h8 _ hJ) hl h).symm.trans e₂))
        · exact Or.inr (Or.inr ((phi_map_eq_zBar A.φ hn hJ (h8 _ hJ) hl h).symm.trans
            (e₃.trans hprod.symm)))
      exact le_iSup_of_le δ (le_iSup_of_le hδ (le_iSup_of_le c (le_iSup_of_le hcond le_rfl)))
    · refine iSup_le fun δ => iSup_le fun hδ => iSup_le fun c => iSup_le fun hcond => ?_
      obtain ⟨J, hJ, hl⟩ := A.label_surj δ hδ c
      obtain ⟨z, hzJ⟩ := hz J hJ
      have ez := phi_map_eq_zBar A.φ hn hJ (h8 _ hJ) hl hzJ
      have hJt : IsUniqueInvolution J t ∨ IsUniqueInvolution J τ ∨
          IsUniqueInvolution J (t * τ) := by
        rcases hcond with h | h | h
        · have : z = t := congrArg Subtype.val (hφ (ez.trans (h.trans e₁.symm)))
          exact Or.inl (this ▸ hzJ)
        · have : z = τ := congrArg Subtype.val (hφ (ez.trans (h.trans e₂.symm)))
          exact Or.inr (Or.inl (this ▸ hzJ))
        · have : z = t * τ :=
            congrArg Subtype.val (hφ (ez.trans (h.trans (hprod.trans e₃.symm))))
          exact Or.inr (Or.inr (this ▸ hzJ))
      have hJM : J ≤ ae6M₀ P t τ := le_iSup₂_of_le J ⟨hJ, hJt⟩ le_rfl
      have hl' : ae6Img A.φ J = AE.memBar δ hδ c := hl
      rw [← hl']
      exact ae6Img_mono hJM
  exact ae6Vertex_of_img hφ A.range_eq (iSup₂_le hS) himg (hModel α β γ hα hβ hγ hprod)
    fun J hJ => ⟨le_pSpan hJ, A.label J hJ⟩

theorem ae6_members_eq {V E M₀ K : Subgroup Y} (v : AE6Vertex V M₀ (ae6ConjIn V K))
    (hME : M₀ ≤ E) (hEV : E ≤ V) (hE : Nat.card E = 86016) (hKM : K ≤ M₀) :
    {J | J ∈ ae6ConjIn V K ∧ J ≤ E} = ae6ConjIn E K := by
  ext J
  constructor
  · rintro ⟨⟨g, hg, rfl⟩, hle⟩
    exact v.orbit E hME hEV hE K ⟨1, V.one_mem, conjSub_one K⟩ _ ⟨g, hg, rfl⟩ (hKM.trans hME) hle
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hEV hg, rfl⟩, conjSub_le_of_mem hg (hKM.trans hME)⟩

end Vertex

section Copies

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem ae6_rep_in_T {W : Subgroup G} (c : Q3CL.Thompson.Ctx Ω W) (hcl : Q3CL.ClassicalClause Ω)
    {t : G} {T : Subgroup G} (hT : IsSylow2In T (Subgroup.centralizer ({t} : Set G)))
    (hWT : W ≤ T) {J : Subgroup G} (hJ : J ∈ Ω) (ht : IsUniqueInvolution J t) :
    ∃ ρ : Rep Ω W, ρ.K = J ∧ ρ.R = T ⊓ J := by
  have hR : IsSylow2In (T ⊓ J) J :=
    AscP1Nine3.isSylow2In_inf_of_isSubnormal hT (hcl.isSubnormal_of_uniqueInvolution hJ ht)
  obtain ⟨S, hTS⟩ := hT.2.1.exists_le_sylow
  have hRD : T ⊓ J ∈ DSet Ω W :=
    Q3CL.Thompson.mem_DSet_of_le_sylow c.hΩ c.hW (hWT.trans hTS) (mem_RSet_of_isSylow2In hJ hR)
      (inf_le_left.trans hTS)
  obtain ⟨r₀, hr₀, hr₀W⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D c.hΩ c.hW hRD
  exact ⟨⟨J, T ⊓ J, r₀, hJ, hRD, hR, hr₀, hr₀W⟩, rfl, rfl⟩

theorem ae6_mem_DSet (hP : Q3CL.PartIHypG Ω) (h2g : ∀ J ∈ Ω, IsPGroup 2 ↥J) {W : Subgroup G}
    (hW : W ∈ WSet Ω) {t : G} (htW : t ∈ W) {J : Subgroup G} (hJ : J ∈ Ω)
    (ht : IsUniqueInvolution J t) : J ∈ DSet Ω W := by
  have c0 : Q3CL.Thompson.Ctx Ω W := Q3CL.T8.ctxOf hP hW
  have hW2 : IsPGroup 2 W := Thompson.isPGroup_of_mem_WSet hW
  have hWC : W ≤ Subgroup.centralizer ({t} : Set G) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (c0.comm_W w hw t htW)
  obtain ⟨T, hT, hWT⟩ := IsSylow2In.exists_ge hW2 hWC
  obtain ⟨ρ, hρK, hρR⟩ := ae6_rep_in_T c0 hP.cls hT hWT hJ ht
  have h1 : ρ.R ∈ DSet Ω W := ρ.hR
  have h2 : IsSylow2In ρ.R ρ.K := ρ.hRK
  rw [hρK] at h2
  rw [hρR] at h1 h2
  have hJT : J = T ⊓ J := h2.2.2 J le_rfl (h2g J hJ) inf_le_right
  rw [← hJT] at h1
  exact h1

variable {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem ae6_adj_of_twins (hd : A7T22.Hyp22G Ω K K' K₃ z u₁ u₂ u₃)
    (hperp : KPerp Ω K = twinSet Ω K) {J J' : Subgroup G} (hJ : J ∈ twinSet Ω K)
    (hJ' : J' ∈ twinSet Ω K) (hne : J' ≠ J) : J' ∈ omegaNbr Ω J := by
  have h1 : KPerp Ω J = KPerp Ω K := A7T22.kPerp_eq_of_twin hd.hyp hd.mem hJ
  have h3 : J' ∈ KPerp Ω J := by rw [h1, hperp]; exact hJ'
  rcases h3 with rfl | h3
  · exact absurd rfl hne
  · exact h3

theorem ae6_not_dbarConnected (hP : Q3CL.PartIHypG Ω)
    (hd : A7T22.Hyp22G Ω K K' K₃ z u₁ u₂ u₃) (hperp : KPerp Ω K = twinSet Ω K)
    {W : Subgroup G} (hW : W ∈ WSet Ω) (ρ₀ : Rep Ω W) (hρ₀ : ρ₀.K = K)
    (hμ : MuIsoWylD4 Ω W) : ¬ DbarConnected Ω W := by
  intro hconn
  have c : Q3CL.Thompson.Ctx Ω W := Q3CL.T8.ctxOf hP hW
  have hover : ∀ ρ : Rep Ω W, ρ.K ∈ twinSet Ω K := by
    intro ρ
    have := Q3T6.Mu.ctx_mem_dComp_of_connected c hconn hd.mem ρ.hK ρ₀.hR ρ.hR (hρ₀ ▸ ρ₀.hRK)
      ρ.hRK
    exact A7T22.dComp_subset_twinSet hd.hyp hd.mem hd.hz hperp this
  have hcomm : ∀ x ∈ muDelta Ω W, ∀ y ∈ muDelta Ω W, x * y = y * x := by
    intro x hx y hy
    obtain ⟨ρ, hρ⟩ := exists_rep_of_mem_muDelta hx
    obtain ⟨σ, hσ⟩ := exists_rep_of_mem_muDelta hy
    apply Subtype.ext
    show (x : NQuot (W ⊔ OCW W)) * y = y * x
    rw [← hρ, ← hσ]
    by_cases hK : σ.K = ρ.K
    · rw [c.img_eq_of_K_eq σ ρ hK]
    · exact c.comm_of_omega ρ σ (ae6_adj_of_twins hd hperp (hover ρ) (hover σ) hK)
  have hcenter : ∀ y ∈ muDelta Ω W, ∀ x : ↥(muGroup Ω W), x * y = y * x := by
    intro y hy x
    have hx : x ∈ Subgroup.closure (muDelta Ω W) := by
      rw [closure_muDelta_eq_top]; trivial
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact hcomm x hx y hy
    | one => simp
    | mul a b _ _ ha hb => rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
    | inv a _ ha =>
      calc a⁻¹ * y = a⁻¹ * (y * a) * a⁻¹ := by group
        _ = a⁻¹ * (a * y) * a⁻¹ := by rw [ha]
        _ = y * a⁻¹ := by group
  have habel : ∀ x y : ↥(muGroup Ω W), x * y = y * x := by
    intro x y
    have hy : y ∈ Subgroup.closure (muDelta Ω W) := by
      rw [closure_muDelta_eq_top]; trivial
    induction hy using Subgroup.closure_induction with
    | mem y hy => exact hcenter y hy x
    | one => simp
    | mul a b _ _ ha hb => rw [← mul_assoc, ha, mul_assoc, hb, ← mul_assoc]
    | inv a _ ha =>
      calc x * a⁻¹ = a⁻¹ * (a * x) * a⁻¹ := by group
        _ = a⁻¹ * (x * a) * a⁻¹ := by rw [ha]
        _ = a⁻¹ * x := by group
  obtain ⟨e⟩ := hμ
  apply s26_coxeterD4_not_comm
  intro u v
  have h1 := habel (e.symm u) (e.symm v)
  calc u * v = e (e.symm u * e.symm v) := by simp
    _ = e (e.symm v * e.symm u) := by rw [h1]
    _ = v * u := by simp

end Copies

theorem exists_inv_conj_q8 {X : Type*} [Group X] {K : Subgroup X}
    (hq : Nonempty (↥K ≃* QuaternionGroup 2)) {a : X} (ha : a ∈ K) (ho : orderOf a = 4) :
    ∃ r ∈ K, r * a * r⁻¹ = a⁻¹ := by
  obtain ⟨e⟩ := hq
  have hQ : ∀ q : QuaternionGroup 2, q * q ≠ 1 → ∃ r : QuaternionGroup 2, r * q * r⁻¹ = q⁻¹ := by
    decide
  have hne : e ⟨a, ha⟩ * e ⟨a, ha⟩ ≠ 1 := by
    rw [← map_mul, ne_eq, MulEquiv.map_eq_one_iff]
    intro h
    have h2 : a * a = 1 := congrArg Subtype.val h
    have h3 : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
    rw [ho] at h3
    norm_num at h3
  obtain ⟨r', hr'⟩ := hQ _ hne
  refine ⟨(e.symm r' : X), (e.symm r').2, ?_⟩
  have h : e.symm r' * ⟨a, ha⟩ * (e.symm r')⁻¹ = (⟨a, ha⟩ : ↥K)⁻¹ := by
    apply e.injective
    rw [map_mul, map_mul, map_inv, map_inv, MulEquiv.apply_symm_apply, hr']
  exact congrArg Subtype.val h

theorem le_ae6L {Y : Type} [Group Y] {Ω : Set (Subgroup Y)} {t τ x : Y} {J : Subgroup Y}
    (hJ : J ∈ ae6Vc Ω t ∪ ae6Vc Ω τ ∪ ae6Vc Ω x) : J ≤ ae6L Ω t τ x :=
  le_iSup₂_of_le J hJ le_rfl

section Config


variable {n : ℕ}

local notation "Ω[" R "]" => CoreAssembly.conjClass (tightCore R)

section Hyp

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y}

theorem ae6_q8 (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) :
    ∀ J ∈ Ω[R], Nonempty (↥J ≃* QuaternionGroup 2) := by
  have h := H.ex.1.perp
  have h2 := H.ex.2.2.2.1
  have hC := CoreData.of_S h.core
  have hK₀q8 : Nonempty (↥(tightCore R) ≃* QuaternionGroup 2) := by
    obtain ⟨P, hP, ⟨e⟩⟩ := hC.datum.exists_sylow_q8 hC.q8
    have hK2 := h2 _ (CoreAssembly.mem_conjClass_self _)
    have hPeq : tightCore R = P := hP.2.2 _ le_rfl hK2 hP.1
    rw [hPeq]
    exact ⟨e⟩
  rintro _ ⟨g, rfl⟩
  obtain ⟨e⟩ := hK₀q8
  exact ⟨(Subgroup.equivMapOfInjective (tightCore R) (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).symm.trans e⟩

theorem ae6_card8 (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) : ∀ J ∈ Ω[R], Nat.card J = 8 := by
  intro J hJ
  obtain ⟨e⟩ := ae6_q8 H J hJ
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem ae6_conj_of_mem_DSet (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) {J₀ : Subgroup Y}
    (hJ₀Ω : J₀ ∈ Ω[R]) (hJ₀D : J₀ ∈ DSet Ω[R] W) : ∃ m ∈ MGrp Ω[R] W, conjSub m K = J₀ := by
  have hStd := H.ex.1
  have hd := hStd.datum
  have hP := (CoreData.of_S hStd.perp.core).partIHypG
  have h2g : ∀ J ∈ Ω[R], IsPGroup 2 ↥J := H.ex.2.2.2.1
  have hK : K ∈ Ω[R] := hd.mem
  have c : Q3CL.Thompson.Ctx Ω[R] W := Q3CL.T8.ctxOf hP H.hW
  have hKsyl : IsSylow2In K K := ⟨le_rfl, h2g K hK, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
  obtain ⟨ρ, hρK⟩ : ∃ ρ : Asc77.Thompson.Rep Ω[R] W, ρ.K = K :=
    ⟨Q3CL.T8.mkRep hP H.hW hK H.hK hKsyl, rfl⟩
  have hJ₀syl : IsSylow2In J₀ J₀ :=
    ⟨le_rfl, h2g J₀ hJ₀Ω, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
  obtain ⟨σ, hσK⟩ : ∃ σ : Asc77.Thompson.Rep Ω[R] W, σ.K = J₀ :=
    ⟨Q3CL.T8.mkRep hP H.hW hJ₀Ω hJ₀D hJ₀syl, rfl⟩
  have hnc : ¬ DbarConnected Ω[R] W :=
    ae6_not_dbarConnected hP hd (kPerp_datum hStd.perp hd.mem hd.hz) H.hW ρ hρK
      (hStd.wyl W H.hW)
  obtain ⟨m, hm, hmK⟩ := c.exists_conj_of_rep hP.cls hnc ρ σ
  exact ⟨m, hm, by rw [← hσK, ← hmK, hρK]⟩

theorem ae6_exists_r (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) {a₁ a₂ a₃ a₄ y : Y}
    (fr : AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y) :
    ∃ r ∈ K, r * (y * t * y⁻¹) * r⁻¹ = t * (y * t * y⁻¹) := by
  have hd := H.ex.1.datum
  have hΩ := hd.hyp
  have h2g : ∀ J ∈ Ω[R], IsPGroup 2 ↥J := H.ex.2.2.2.1
  have hF := H.ex.2.1
  obtain ⟨r, hr, hra⟩ := exists_inv_conj_q8 (ae6_q8 H K hd.mem) fr.h₁.1 fr.o₁
  have hz₄ : IsUniqueInvolution K₄ t := Asc77.isUniqueInvolution_of_mem_twinSet hd.hz hF.1
  have hcomm : ∀ {L : Subgroup Y}, L ∈ Ω[R] → L ≠ K → IsUniqueInvolution L t → ∀ a ∈ L,
      r * a * r⁻¹ = a := by
    intro L hL hne hzL a ha
    rw [commute_of_trivialOnQuot (h2g L hL)
      (A7T22.le_trivialOnQuot_of_twin hΩ hd.mem hL hne.symm hd.hz hzL hr) ha,
      mul_inv_cancel_right]
  have e2 := hcomm hd.hK'.1 hd.hne hd.hzK' a₂ fr.h₂.1
  have e3 := hcomm hd.hK₃.1 hd.hK₃K hd.hzK₃ a₃ fr.h₃.1
  have e4 := hcomm hF.1.1 hF.2.1 hz₄ a₄ fr.h₄.1
  have hsq : a₁ * a₁ = t := Asc77.sq_eq_of_orderOf_four hd.hz fr.h₁.1 fr.o₁
  have h4 : a₁ ^ 4 = 1 := fr.o₁ ▸ pow_orderOf_eq_one a₁
  have hinv : a₁⁻¹ = t * a₁ := by
    rw [← hsq]
    refine inv_eq_of_mul_eq_one_right ?_
    calc a₁ * (a₁ * a₁ * a₁) = a₁ ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := h4
  refine ⟨r, hr, ?_⟩
  rw [fr.hy]
  calc r * (a₁ * a₂ * a₃ * a₄) * r⁻¹
      = (r * a₁ * r⁻¹) * (r * a₂ * r⁻¹) * (r * a₃ * r⁻¹) * (r * a₄ * r⁻¹) := by group
    _ = t * (a₁ * a₂ * a₃ * a₄) := by rw [hra, e2, e3, e4, hinv]; group

end Hyp

theorem v3AE6Shape_of (hI : V3AE6I n) (hL : V3AE6L n) (hModel : AE6ModelPar) : V3AE6Shape n := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y h H fr hx L₂ L₃ A₂ A₃ hD
  have hStd := H.ex.1
  have hd := hStd.datum
  have hΩ : HypOmegaGen Ω[R] := hd.hyp
  have hP := (CoreData.of_S hStd.perp.core).partIHypG
  have h2g : ∀ J ∈ Ω[R], IsPGroup 2 ↥J := H.ex.2.2.2.1
  have hinv := conjInvariant_conjClass (tightCore R)
  obtain ⟨-, A, hAspan, hAker, hAO⟩ := hI Y R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y H fr
  obtain ⟨-, -, hLspan, B, hBker⟩ := hL Y R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y h H fr hx
  obtain ⟨hMl₂, hMl₃, hL₂I, hL₃I, hne, hxA₂, hxA₃, -, -, -, -, -, -, -, -,
    ⟨B₂, hB₂span, hB₂ker, hB₂O⟩, ⟨B₃, hB₃span, hB₃ker, hB₃O⟩⟩ := hD
  have hxD : h * (y * t * y⁻¹) * h⁻¹ ∉ ae6D Ω[R] W (u₁ * u₂) := hx.2.1
  have htW : t ∈ W := hd.sq₁ ▸ W.mul_mem H.hu₁ H.hu₁
  have hτW : y * t * y⁻¹ ∈ W := by
    rw [fr.hy]
    exact W.mul_mem (W.mul_mem (W.mul_mem fr.h₁.2 fr.h₂.2) fr.h₃.2) fr.h₄.2
  have hKy : IsUniqueInvolution (conjSub y K) (y * t * y⁻¹) := hd.hz.conj y
  have hKyΩ : conjSub y K ∈ Ω[R] := hinv y K hd.mem
  obtain ⟨m, hm, hmK⟩ := ae6_conj_of_mem_DSet H hKyΩ (ae6_mem_DSet hP h2g H.hW hτW hKyΩ hKy)
  obtain ⟨r, hr, hrτ⟩ := ae6_exists_r H fr
  have hKM : K ≤ MGrp Ω[R] W := le_iSup₂_of_le K H.hK le_rfl
  have hrM : r ∈ MGrp Ω[R] W := hKM hr
  have hJτ : IsUniqueInvolution (conjSub m K) (y * t * y⁻¹) := hmK ▸ hKy
  have hJtτ : IsUniqueInvolution (conjSub (r * m) K) (t * (y * t * y⁻¹)) := by
    rw [conjSub_mul, hmK]
    have h1 := hKy.conj r
    rwa [hrτ] at h1
  have hPΩ : ∀ (X : Subgroup Y), ∀ J ∈ ae6ConjIn X K, J ∈ Ω[R] := by
    rintro X J ⟨g, -, rfl⟩
    exact hinv g K hd.mem
  have hM₀M : ∀ X : Subgroup Y, ae6M₀ (ae6ConjIn X K) t (y * t * y⁻¹) ≤ MGrp Ω[R] W := by
    intro X
    refine iSup₂_le fun J hJ => ?_
    obtain ⟨hJX, hJt⟩ := hJ
    have hJΩ := hPΩ X J hJX
    rcases hJt with h' | h' | h'
    · exact le_iSup₂_of_le J (ae6_mem_DSet hP h2g H.hW htW hJΩ h') le_rfl
    · exact le_iSup₂_of_le J (ae6_mem_DSet hP h2g H.hW hτW hJΩ h') le_rfl
    · exact le_iSup₂_of_le J (ae6_mem_DSet hP h2g H.hW (W.mul_mem htW hτW) hJΩ h') le_rfl
  have hKL : K ≤ ae6L Ω[R] t (y * t * y⁻¹) (h * (y * t * y⁻¹) * h⁻¹) :=
    le_ae6L (Or.inl (Or.inl ⟨hd.mem, hd.hz⟩))
  have hrL := hKL hr
  have hM₀L : ∀ X : Subgroup Y, ae6M₀ (ae6ConjIn X K) t (y * t * y⁻¹) ≤
      ae6L Ω[R] t (y * t * y⁻¹) (h * (y * t * y⁻¹) * h⁻¹) := by
    intro X
    refine iSup₂_le fun J hJ => ?_
    obtain ⟨hJX, hJt⟩ := hJ
    have hJΩ := hPΩ X J hJX
    rcases hJt with h' | h' | h'
    · exact le_ae6L (Or.inl (Or.inl ⟨hJΩ, h'⟩))
    · exact le_ae6L (Or.inl (Or.inr ⟨hJΩ, h'⟩))
    · have h1 : IsUniqueInvolution (conjSub r⁻¹ J) (y * t * y⁻¹) := by
        have h2 := h'.conj r⁻¹
        rwa [show r⁻¹ * (t * (y * t * y⁻¹)) * r⁻¹⁻¹ = y * t * y⁻¹ by rw [← hrτ]; group] at h2
      have h3 : conjSub r⁻¹ J ≤ ae6L Ω[R] t (y * t * y⁻¹) (h * (y * t * y⁻¹) * h⁻¹) :=
        le_ae6L (Or.inl (Or.inr ⟨hinv _ J hJΩ, h1⟩))
      calc J = conjSub r (conjSub r⁻¹ J) := (conjSub_conjSub_inv r J).symm
        _ ≤ conjSub r _ := conjSub_mono h3
        _ = _ := conjSub_eq_self_of_mem hrL
  have hvert : ∀ (X : Subgroup Y), MGrp Ω[R] W ≤ X → ∀ (C : AEIdent (ae6ConjIn X K) 8),
      C.φ.ker = ⊥ → pSpan (ae6ConjIn X K) = X →
        AE6Vertex X (ae6M₀ (ae6ConjIn X K) t (y * t * y⁻¹)) (ae6ConjIn X K) := by
    intro X hMX C hker hspan
    have hv := ae6Vertex_of_ident hModel C hker (fun J hJ => ae6_card8 H J (hPΩ X J hJ))
      (fun J hJ => Sec6Gen.exists_uniqueInvolution hΩ (hPΩ X J hJ))
      (⟨1, X.one_mem, conjSub_one K⟩ : K ∈ ae6ConjIn X K)
      (⟨m, hMX hm, rfl⟩ : conjSub m K ∈ ae6ConjIn X K)
      (⟨r * m, X.mul_mem (hMX hrM) (hMX hm), rfl⟩ : conjSub (r * m) K ∈ ae6ConjIn X K)
      hd.hz hJτ hJtτ
    rwa [hspan] at hv
  have hMI : MGrp Ω[R] W ≤ ae6I Ω[R] W (u₁ * u₂) := le_sup_left
  have v₁ := hvert _ hMI A hAker hAspan
  have v₂ := hvert _ (hMl₃.trans le_sup_right) B₂ hB₂ker hB₂span
  have v₃ := hvert _ (hMl₂.trans le_sup_right) B₃ hB₃ker hB₃span
  have hLcard : Nat.card (ae6L Ω[R] t (y * t * y⁻¹) (h * (y * t * y⁻¹) * h⁻¹)) =
      Nat.card AE.e29Sub := by
    have hφ : Function.Injective B.φ := (MonoidHom.ker_eq_bot_iff _).mp hBker
    have h1 := Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv
    rwa [B.range_eq, hLspan] at h1
  clear hAker A hB₂ker B₂ hB₃ker B₃ hBker B
  set M := MGrp Ω[R] W with hMdef
  set I := ae6I Ω[R] W (u₁ * u₂) with hIdef
  set L := ae6L Ω[R] t (y * t * y⁻¹) (h * (y * t * y⁻¹) * h⁻¹) with hLdef
  set M₁ := ae6M₀ (ae6ConjIn I K) t (y * t * y⁻¹) with hM₁def
  have hM₁M : M₁ ≤ M := hM₀M I
  have hM₁L : M₁ ≤ L := hM₀L I
  have hL8 : Nat.card L ≠ Nat.card ae6AE8 := by
    rw [hLcard]
    intro h'
    exact e29Sub_ne (Subgroup.eq_of_le_of_card_ge e29Sub_le h'.ge)
  have hcardI : ∀ X : Subgroup Y, X ≤ I → Nat.card X = Nat.card ae6AE8 → X = I :=
    fun X hX hc => Subgroup.eq_of_le_of_card_ge hX (by rw [v₁.iso, hc])
  have hV₂I : ¬ L ⊔ L₃ ≤ I := by
    intro hle
    apply hxD
    rw [← hAO, ← hcardI _ hle v₂.iso, hB₂O]
    exact hxA₂
  have hV₃I : ¬ L ⊔ L₂ ≤ I := by
    intro hle
    apply hxD
    rw [← hAO, ← hcardI _ hle v₃.iso, hB₃O]
    exact hxA₃
  have hIV₂ : ¬ I ≤ L ⊔ L₃ := fun hle =>
    hV₂I (Subgroup.eq_of_le_of_card_ge hle (by rw [v₁.iso, v₂.iso])).ge
  have hIV₃ : ¬ I ≤ L ⊔ L₂ := fun hle =>
    hV₃I (Subgroup.eq_of_le_of_card_ge hle (by rw [v₁.iso, v₃.iso])).ge
  have hL₃86 : Nat.card L₃ = 86016 := by
    rcases v₁.overg L₃ (hM₁M.trans hMl₃) hL₃I with h' | h' | h'
    · exact (hL8 (by rw [← v₂.iso, sup_eq_left.mpr (h'.le.trans hM₁L)])).elim
    · exact (hIV₂ (h'.symm.le.trans le_sup_right)).elim
    · exact h'
  have hL₂86 : Nat.card L₂ = 86016 := by
    rcases v₁.overg L₂ (hM₁M.trans hMl₂) hL₂I with h' | h' | h'
    · exact (hL8 (by rw [← v₃.iso, sup_eq_left.mpr (h'.le.trans hM₁L)])).elim
    · exact (hIV₃ (h'.symm.le.trans le_sup_right)).elim
    · exact h'
  have hL₂L₃ : L₂ ⊓ L₃ = M₁ :=
    v₁.inf (hM₁M.trans hMl₂) (hM₁M.trans hMl₃) hL₂I hL₂86 hL₃86 hne
  have hMeq : M = M₁ := le_antisymm ((le_inf hMl₂ hMl₃).trans hL₂L₃.le) hM₁M
  have hMcard : Nat.card M = 12288 := by rw [hMeq]; exact v₁.card
  have hML : M ≤ L := hMeq.le.trans hM₁L
  have hIV₂eq : I ⊓ (L ⊔ L₃) = L₃ := by
    have hle : L₃ ≤ I ⊓ (L ⊔ L₃) := le_inf hL₃I le_sup_right
    rcases v₁.overg _ ((hM₁M.trans hMl₃).trans hle) inf_le_left with h' | h' | h'
    · have h1 := Subgroup.card_le_of_le (hle.trans h'.le)
      rw [hL₃86, v₁.card] at h1
      norm_num at h1
    · exact (hIV₂ (inf_eq_left.mp h')).elim
    · exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h', hL₃86])).symm
  have hIV₃eq : I ⊓ (L ⊔ L₂) = L₂ := by
    have hle : L₂ ≤ I ⊓ (L ⊔ L₂) := le_inf hL₂I le_sup_right
    rcases v₁.overg _ ((hM₁M.trans hMl₂).trans hle) inf_le_left with h' | h' | h'
    · have h1 := Subgroup.card_le_of_le (hle.trans h'.le)
      rw [hL₂86, v₁.card] at h1
      norm_num at h1
    · exact (hIV₃ (inf_eq_left.mp h')).elim
    · exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h', hL₂86])).symm
  have hM₂ : ae6M₀ (ae6ConjIn (L ⊔ L₃) K) t (y * t * y⁻¹) = M :=
    Subgroup.eq_of_le_of_card_ge (hM₀M _) (by rw [hMcard, v₂.card])
  have hM₃ : ae6M₀ (ae6ConjIn (L ⊔ L₂) K) t (y * t * y⁻¹) = M :=
    Subgroup.eq_of_le_of_card_ge (hM₀M _) (by rw [hMcard, v₃.card])
  rw [hM₂] at v₂
  rw [hM₃] at v₃
  rw [← hMeq] at v₁
  have hL86 : Nat.card L = 86016 := by
    rcases v₂.overg L hML le_sup_left with h' | h' | h'
    · exact (hV₂I (sup_le (h'.le.trans hMI) hL₃I)).elim
    · exact (hL8 (by rw [← v₂.iso, ← h'])).elim
    · exact h'
  have hV₂V₃ : (L ⊔ L₃) ⊓ (L ⊔ L₂) = L := by
    have hle : L ≤ (L ⊔ L₃) ⊓ (L ⊔ L₂) := le_inf le_sup_left le_sup_left
    rcases v₂.overg _ (hML.trans hle) inf_le_left with h' | h' | h'
    · have h1 := Subgroup.card_le_of_le (hle.trans h'.le)
      rw [hL86, hMcard] at h1
      norm_num at h1
    · have heq : L ⊔ L₃ = L ⊔ L₂ :=
        Subgroup.eq_of_le_of_card_ge (inf_eq_left.mp h') (by rw [v₂.iso, v₃.iso])
      exact (hne (by rw [← hIV₃eq, ← heq, hIV₂eq])).elim
    · exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h', hL86])).symm
  refine ⟨hML, hIV₂eq, hIV₃eq, hV₂V₃, hL₂L₃.trans hMeq.symm, hMcard, ?_, ?_⟩
  · intro k l hkl
    fin_cases k <;> fin_cases l
    · exact absurd rfl hkl
    · show pCoreOf 2 I ≤ I ⊓ (L ⊔ L₃) ∧ Nat.card ↥(I ⊓ (L ⊔ L₃)) = 86016
      rw [hIV₂eq]
      exact ⟨v₁.pCoreOf_le hMl₃ hL₃I hL₃86, hL₃86⟩
    · show pCoreOf 2 I ≤ I ⊓ (L ⊔ L₂) ∧ Nat.card ↥(I ⊓ (L ⊔ L₂)) = 86016
      rw [hIV₃eq]
      exact ⟨v₁.pCoreOf_le hMl₂ hL₂I hL₂86, hL₂86⟩
    · show pCoreOf 2 (L ⊔ L₃) ≤ (L ⊔ L₃) ⊓ I ∧ Nat.card ↥((L ⊔ L₃) ⊓ I) = 86016
      rw [inf_comm (L ⊔ L₃) I, hIV₂eq]
      exact ⟨v₂.pCoreOf_le hMl₃ le_sup_right hL₃86, hL₃86⟩
    · exact absurd rfl hkl
    · show pCoreOf 2 (L ⊔ L₃) ≤ (L ⊔ L₃) ⊓ (L ⊔ L₂) ∧ Nat.card ↥((L ⊔ L₃) ⊓ (L ⊔ L₂)) = 86016
      rw [hV₂V₃]
      exact ⟨v₂.pCoreOf_le hML le_sup_left hL86, hL86⟩
    · show pCoreOf 2 (L ⊔ L₂) ≤ (L ⊔ L₂) ⊓ I ∧ Nat.card ↥((L ⊔ L₂) ⊓ I) = 86016
      rw [inf_comm (L ⊔ L₂) I, hIV₃eq]
      exact ⟨v₃.pCoreOf_le hMl₂ le_sup_right hL₂86, hL₂86⟩
    · show pCoreOf 2 (L ⊔ L₂) ≤ (L ⊔ L₂) ⊓ (L ⊔ L₃) ∧ Nat.card ↥((L ⊔ L₂) ⊓ (L ⊔ L₃)) = 86016
      rw [inf_comm (L ⊔ L₂) (L ⊔ L₃), hV₂V₃]
      exact ⟨v₃.pCoreOf_le hML le_sup_left hL86, hL86⟩
    · exact absurd rfl hkl
  · intro k l hkl
    fin_cases k <;> fin_cases l
    · exact absurd rfl hkl
    · show {J | J ∈ ae6ConjIn I K ∧ J ≤ I ⊓ (L ⊔ L₃)} = ae6ConjIn (I ⊓ (L ⊔ L₃)) K
      rw [hIV₂eq]
      exact ae6_members_eq v₁ hMl₃ hL₃I hL₃86 hKM
    · show {J | J ∈ ae6ConjIn I K ∧ J ≤ I ⊓ (L ⊔ L₂)} = ae6ConjIn (I ⊓ (L ⊔ L₂)) K
      rw [hIV₃eq]
      exact ae6_members_eq v₁ hMl₂ hL₂I hL₂86 hKM
    · show {J | J ∈ ae6ConjIn (L ⊔ L₃) K ∧ J ≤ (L ⊔ L₃) ⊓ I} = ae6ConjIn ((L ⊔ L₃) ⊓ I) K
      rw [inf_comm (L ⊔ L₃) I, hIV₂eq]
      exact ae6_members_eq v₂ hMl₃ le_sup_right hL₃86 hKM
    · exact absurd rfl hkl
    · show {J | J ∈ ae6ConjIn (L ⊔ L₃) K ∧ J ≤ (L ⊔ L₃) ⊓ (L ⊔ L₂)} =
        ae6ConjIn ((L ⊔ L₃) ⊓ (L ⊔ L₂)) K
      rw [hV₂V₃]
      exact ae6_members_eq v₂ hML le_sup_left hL86 hKM
    · show {J | J ∈ ae6ConjIn (L ⊔ L₂) K ∧ J ≤ (L ⊔ L₂) ⊓ I} = ae6ConjIn ((L ⊔ L₂) ⊓ I) K
      rw [inf_comm (L ⊔ L₂) I, hIV₃eq]
      exact ae6_members_eq v₃ hMl₂ le_sup_right hL₂86 hKM
    · show {J | J ∈ ae6ConjIn (L ⊔ L₂) K ∧ J ≤ (L ⊔ L₂) ⊓ (L ⊔ L₃)} =
        ae6ConjIn ((L ⊔ L₂) ⊓ (L ⊔ L₃)) K
      rw [inf_comm (L ⊔ L₂) (L ⊔ L₃), hV₂V₃]
      exact ae6_members_eq v₃ hML le_sup_left hL86 hKM
    · exact absurd rfl hkl

end Config

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.A6h1
