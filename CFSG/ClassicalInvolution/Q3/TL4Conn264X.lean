module

public import CFSG.ClassicalInvolution.Q3.TL4Conn264T
public import CFSG.ClassicalInvolution.Q3.TL4Conn26YS
public import CFSG.ClassicalInvolution.Q3.TL4LinkE2Gen
public import CFSG.ClassicalInvolution.Q3.TL4SecIdE2AEM

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.T8 (XMem)
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin (pSpan le_pSpan ThmDHyp AEIdent AEIdentOn
  phi_map_eq_zBar)
open CFSG.ClassicalInvolution.Q3.AE (AEQ memBar zBar)

theorem mem_normalizer_of_conj_mem {G : Type} [Group G] [Finite G] {H : Subgroup G} {g : G}
    (h : ∀ a ∈ H, g * a * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  have hle : conjSub g H ≤ H := by
    rintro _ ⟨a, ha, rfl⟩
    exact h a ha
  have heq : conjSub g H = H := Subgroup.eq_of_le_of_card_ge hle (le_of_eq
    (Nat.card_congr (H.equivMapOfInjective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).toEquiv))
  exact mem_normalizer_iff_conjSub_eq.mpr heq

theorem le_normalizer_of_comm {G : Type} [Group G] {A B : Subgroup G}
    (h : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) : A ≤ Subgroup.normalizer (B : Set G) := fun x hx =>
  Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy =>
    (h x hx y hy).symm)

theorem exists_quad {m : ℕ} {γ δ : Finset (Fin m)} (hγ : 2 ≤ γ.card) (hδ : 2 ≤ δ.card)
    (hd : Disjoint γ δ) : ∃ (p q : Fin m) (β : Finset (Fin m)) (_ : β.card = 4),
      p ∈ β ∧ q ∈ β ∧ p ≠ q ∧ γ ∩ β = {p, q} ∧ δ ∩ β = β \ {p, q} ∧ ¬ β ⊆ γ ∧ ¬ β ⊆ δ := by
  classical
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (by omega : 1 < γ.card)
  obtain ⟨r, hr, s, hs, hrs⟩ := Finset.one_lt_card.mp (by omega : 1 < δ.card)
  have hpδ : p ∉ δ := Finset.disjoint_left.mp hd hp
  have hqδ : q ∉ δ := Finset.disjoint_left.mp hd hq
  have hrγ : r ∉ γ := Finset.disjoint_right.mp hd hr
  have hsγ : s ∉ γ := Finset.disjoint_right.mp hd hs
  have hpr : p ≠ r := fun e => hpδ (e ▸ hr)
  have hps : p ≠ s := fun e => hpδ (e ▸ hs)
  have hqr : q ≠ r := fun e => hqδ (e ▸ hr)
  have hqs : q ≠ s := fun e => hqδ (e ▸ hs)
  refine ⟨p, q, {p, q, r, s}, ?_, by simp, by simp, hpq, ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem (by simp [hpq, hpr, hps]),
      Finset.card_insert_of_notMem (by simp [hqr, hqs]), Finset.card_pair hrs]
  · ext x
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hx, h | h | h | h⟩
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd (h ▸ hx) hrγ
      · exact absurd (h ▸ hx) hsγ
    · rintro (h | h)
      · exact ⟨h ▸ hp, Or.inl h⟩
      · exact ⟨h ▸ hq, Or.inr (Or.inl h)⟩
  · ext x
    simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hx, h | h | h | h⟩
      · exact absurd (h ▸ hx) hpδ
      · exact absurd (h ▸ hx) hqδ
      · refine ⟨Or.inr (Or.inr (Or.inl h)), ?_⟩
        rintro (h' | h')
        · exact hpr (h'.symm.trans h)
        · exact hqr (h'.symm.trans h)
      · refine ⟨Or.inr (Or.inr (Or.inr h)), ?_⟩
        rintro (h' | h')
        · exact hps (h'.symm.trans h)
        · exact hqs (h'.symm.trans h)
    · rintro ⟨h | h | h | h, hn⟩
      · exact absurd (Or.inl h) hn
      · exact absurd (Or.inr h) hn
      · exact ⟨h ▸ hr, Or.inr (Or.inr (Or.inl h))⟩
      · exact ⟨h ▸ hs, Or.inr (Or.inr (Or.inr h))⟩
  · intro h
    exact hrγ (h (by simp))
  · intro h
    exact hpδ (h (by simp))

theorem memBar_le_normalizer_twin {m : ℕ} {γ : Finset (Fin m)} (h₁ h₂ : γ.card = 4)
    (b₁ b₂ : Bool) : memBar γ h₁ b₁ ≤ Subgroup.normalizer (memBar γ h₂ b₂ : Set (AEQ m)) := by
  cases b₁ <;> cases b₂
  · exact Subgroup.le_normalizer
  · exact le_normalizer_of_comm fun x hx y hy => (SecIdE2.comm_memBar_twin γ h₁ y hy x hx).symm
  · exact le_normalizer_of_comm fun x hx y hy => SecIdE2.comm_memBar_twin γ h₁ x hx y hy
  · exact Subgroup.le_normalizer

section Cit3


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {Rd : Subgroup Y} {Sd : Sylow 2 Rd} {z : Y}
  {J : Subgroup Y} {S : Sylow 2 Y} {R T W : Subgroup Y} {t : Y}

theorem TightStd8R.false_of_three_labels (hs : TightStd8R 3 n Rd Sd z J S R T W t)
    (hE : MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W)
    (hD : ThmDHyp 3 (restrictFamily (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t))
      (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t))))
    {m : ℕ} (hm : 5 ≤ m)
    (φ : ↥(pSpan (restrictFamily (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t))
      (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t)))) →* AEQ m)
    (hker : φ.ker ≤ Subgroup.center _)
    (hKX : secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) (tightCore Rd) ≤
      secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t))
    (hJX : secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) J ≤
      secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t))
    {L : Subgroup Y} (hL : XMem (CoreAssembly.conjClass (tightCore Rd)) (z * t) L)
    {γ₁ γ₂ β : Finset (Fin m)} {h₁ : γ₁.card = 4} {h₂ : γ₂.card = 4} {hβ : β.card = 4}
    {b₁ b₂ : Bool}
    (hlK : (((secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) (tightCore Rd)).subgroupOf
      (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t))).subgroupOf
        (pSpan (restrictFamily (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t))
          (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t))))).map φ =
      memBar γ₁ h₁ b₁)
    (hlJ : (((secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) J).subgroupOf
      (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t))).subgroupOf
        (pSpan (restrictFamily (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t))
          (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t))))).map φ =
      memBar γ₂ h₂ b₂)
    (hlL : (((secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) L).subgroupOf
      (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t))).subgroupOf
        (pSpan (restrictFamily (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t))
          (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t))))).map φ =
      memBar β hβ true)
    {v : AEQ m} (hvβ : v ∈ memBar β hβ true) (hv2 : v * v ≠ 1)
    (hv₁ : ∀ a ∈ memBar γ₁ h₁ b₁, v * a * v⁻¹ ∈ memBar γ₁ h₁ b₁)
    (hv₂ : ∀ a ∈ memBar γ₂ h₂ b₂, v * a * v⁻¹ ∈ memBar γ₂ h₂ b₂)
    (h12 : memBar γ₁ h₁ b₁ ≤ Subgroup.normalizer (memBar γ₂ h₂ b₂ : Set (AEQ m)))
    (hvK : v ∉ memBar γ₁ h₁ b₁) (hvJ : v ∉ memBar γ₂ h₂ b₂) : False := by
  have h := TightLargeHypR.typeRFam hs.large
  have hΦ := h.secFam (x := z * t)
  have hKΦ := secImg_mem hs.xMem_K
  have hJΦ := secImg_mem hs.xMem_J
  have hLΦ := secImg_mem hL
  have hmem2 : ∀ (γ : Finset (Fin m)) (hγ : γ.card = 4) (c : Bool),
      IsPGroup 2 ↥(memBar γ hγ c) := fun γ hγ c =>
    IsPGroup.of_card (n := 3) (by rw [AE.natCard_memBar hm]; norm_num)
  have hQ₀ : IsPGroup 2 ↥(memBar γ₁ h₁ b₁ ⊔ memBar γ₂ h₂ b₂) :=
    (hmem2 γ₁ h₁ b₁).to_sup_of_normal_right' (hmem2 γ₂ h₂ b₂) h12
  have hvN : Subgroup.zpowers v ≤
      Subgroup.normalizer ((memBar γ₁ h₁ b₁ ⊔ memBar γ₂ h₂ b₂ : Subgroup (AEQ m)) :
        Set (AEQ m)) := by
    rw [Subgroup.zpowers_le]
    have e₁ := mem_normalizer_iff_conjSub_eq.mp (mem_normalizer_of_conj_mem hv₁)
    have e₂ := mem_normalizer_iff_conjSub_eq.mp (mem_normalizer_of_conj_mem hv₂)
    refine mem_normalizer_iff_conjSub_eq.mpr ?_
    show (memBar γ₁ h₁ b₁ ⊔ memBar γ₂ h₂ b₂).map (MulAut.conj v).toMonoidHom = _
    rw [Subgroup.map_sup]
    exact congrArg₂ (· ⊔ ·) e₁ e₂
  have hv2g : IsPGroup 2 ↥(Subgroup.zpowers v) :=
    (hmem2 β hβ true).to_le (Subgroup.zpowers_le.mpr hvβ)
  have hQ : IsPGroup 2 ↥(Subgroup.zpowers v ⊔ (memBar γ₁ h₁ b₁ ⊔ memBar γ₂ h₂ b₂)) :=
    hv2g.to_sup_of_normal_right' hQ₀ hvN
  have hP2 := ((hQ.comap_of_ker_isPGroup φ (LinkE2.isPGroup_ker hD hker)).map
    (pSpan (restrictFamily (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t))
      (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t)))).subtype).map
    (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t)).subtype
  have hin : ∀ {M : Subgroup (SecQuot (CoreAssembly.conjClass (tightCore Rd)) (z * t))},
      M ∈ secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t) →
      ∀ hMX : M ≤ secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t),
      ∀ {γ : Finset (Fin m)} {hγ : γ.card = 4} {c : Bool},
      ((M.subgroupOf (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd)
        (z * t))).subgroupOf (pSpan (restrictFamily
          (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t))
          (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t))))).map φ =
        memBar γ hγ c →
      memBar γ hγ c ≤ Subgroup.zpowers v ⊔ (memBar γ₁ h₁ b₁ ⊔ memBar γ₂ h₂ b₂) →
      M ≤ (((Subgroup.zpowers v ⊔ (memBar γ₁ h₁ b₁ ⊔ memBar γ₂ h₂ b₂)).comap φ).map
        (pSpan (restrictFamily (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t))
          (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t)))).subtype).map
        (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t)).subtype := by
    intro M hM hMX γ hγ c hlab hle x hx
    have hxS : (⟨x, hMX hx⟩ : ↥(secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd)
        (z * t))) ∈ pSpan (restrictFamily (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t))
          (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t))) :=
      le_pSpan (P := restrictFamily (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t))
        (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t)))
        (L := M.subgroupOf (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t)))
        ⟨M, hM, hMX, rfl⟩ (Subgroup.mem_subgroupOf.mpr hx)
    refine Subgroup.mem_map.mpr ⟨⟨x, hMX hx⟩,
      Subgroup.mem_map.mpr ⟨⟨⟨x, hMX hx⟩, hxS⟩, ?_, rfl⟩, rfl⟩
    rw [Subgroup.mem_comap]
    apply hle
    rw [← hlab]
    exact ⟨⟨⟨x, hMX hx⟩, hxS⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hKP := hin hKΦ hKX hlK (le_sup_left.trans le_sup_right)
  have hJP := hin hJΦ hJX hlJ (le_sup_right.trans le_sup_right)
  have hvβ' := hvβ
  rw [← hlL] at hvβ'
  obtain ⟨y, hy, hyv⟩ := hvβ'
  have hyL : ((y : ↥(secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t))) :
      SecQuot (CoreAssembly.conjClass (tightCore Rd)) (z * t)) ∈
      secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) L :=
    Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hy)
  have hzp : Subgroup.zpowers ((y : ↥(secOrb (CoreAssembly.conjClass (tightCore Rd))
      (tightCore Rd) (z * t))) : SecQuot (CoreAssembly.conjClass (tightCore Rd)) (z * t)) ≤
      secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) L ⊓
        (((Subgroup.zpowers v ⊔ (memBar γ₁ h₁ b₁ ⊔ memBar γ₂ h₂ b₂)).comap φ).map
          (pSpan (restrictFamily (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t))
            (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t)))).subtype).map
          (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t)).subtype := by
    rintro _ ⟨k, rfl⟩
    refine ⟨Subgroup.zpow_mem _ hyL k, Subgroup.mem_map.mpr ⟨(y : ↥(secOrb
      (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t))) ^ k,
      Subgroup.mem_map.mpr ⟨y ^ k, ?_, rfl⟩, ?_⟩⟩
    · rw [Subgroup.mem_comap, map_zpow, hyv]
      exact Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers v k)
    · simp
  have hy2 : ((y : ↥(secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t))) :
      SecQuot (CoreAssembly.conjClass (tightCore Rd)) (z * t)) ^ 2 ≠ 1 := by
    intro e
    apply hv2
    have e' : y ^ 2 = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      simpa using e
    rw [← hyv, ← map_mul, ← pow_two, e', map_one]
  have hord : 2 < orderOf ((y : ↥(secOrb (CoreAssembly.conjClass (tightCore Rd))
      (tightCore Rd) (z * t))) : SecQuot (CoreAssembly.conjClass (tightCore Rd)) (z * t)) := by
    have hnd : ¬ orderOf ((y : ↥(secOrb (CoreAssembly.conjClass (tightCore Rd))
        (tightCore Rd) (z * t))) : SecQuot (CoreAssembly.conjClass (tightCore Rd)) (z * t)) ∣ 2 :=
      fun hd => hy2 (orderOf_dvd_iff_pow_eq_one.mp hd)
    have h0 := orderOf_pos ((y : ↥(secOrb (CoreAssembly.conjClass (tightCore Rd))
      (tightCore Rd) (z * t))) : SecQuot (CoreAssembly.conjClass (tightCore Rd)) (z * t))
    have h1 : orderOf ((y : ↥(secOrb (CoreAssembly.conjClass (tightCore Rd))
        (tightCore Rd) (z * t))) : SecQuot (CoreAssembly.conjClass (tightCore Rd)) (z * t)) ≠ 1 :=
      fun e => hy2 (by rw [orderOf_eq_one_iff.mp e, one_pow])
    have h2 : orderOf ((y : ↥(secOrb (CoreAssembly.conjClass (tightCore Rd))
        (tightCore Rd) (z * t))) : SecQuot (CoreAssembly.conjClass (tightCore Rd)) (z * t)) ≠ 2 :=
      fun e => hy2 (by rw [← e]; exact pow_orderOf_eq_one _)
    omega
  have hcL : 2 < Nat.card ↥(secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) L ⊓
      (((Subgroup.zpowers v ⊔ (memBar γ₁ h₁ b₁ ⊔ memBar γ₂ h₂ b₂)).comap φ).map
        (pSpan (restrictFamily (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t))
          (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t)))).subtype).map
        (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t)).subtype) := by
    refine lt_of_lt_of_le ?_ (Subgroup.card_le_of_le hzp)
    rw [Nat.card_zpowers]
    exact hord
  have hcard : ∀ {M : Subgroup (SecQuot (CoreAssembly.conjClass (tightCore Rd)) (z * t))},
      M ∈ secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t) →
      M ≤ secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t) →
      ∀ {P : Subgroup (SecQuot (CoreAssembly.conjClass (tightCore Rd)) (z * t))}, M ≤ P →
        2 < Nat.card ↥(M ⊓ P) := by
    intro M hM hMX P hMP
    rw [inf_eq_left.mpr hMP, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMX).toEquiv,
      hD.card _ ⟨M, hM, hMX, rfl⟩]
    norm_num
  have hKL : secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) (tightCore Rd) ≠
      secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) L := by
    intro e
    apply hvK
    rw [← hlK, e, hlL]
    exact hvβ
  have hJL : secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) J ≠
      secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) L := by
    intro e
    apply hvJ
    rw [← hlJ, e, hlL]
    exact hvβ
  exact false_of_three_secImg_E4 hs.partIHypG hs.hW.1 hE hs.xMem_K hs.xMem_J hL
    hs.secImg_J_mem_omegaNbr.2.1.symm hKL hJL hP2 (hcard hKΦ hKX hKP)
    (hcard hJΦ hJX hJP) hcL

theorem TightStd8R.labels_eq_or_disjoint (hs : TightStd8R 3 n Rd Sd z J S R T W t)
    (hD : ThmDHyp 3 (restrictFamily (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t))
      (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t))))
    {m : ℕ} (hm : 5 ≤ m)
    (φ : ↥(pSpan (restrictFamily (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t))
      (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t)))) →* AEQ m)
    (hKX : secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) (tightCore Rd) ≤
      secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t))
    (hJX : secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) J ≤
      secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t))
    {γ₁ γ₂ : Finset (Fin m)} {h₁ : γ₁.card = 4} {h₂ : γ₂.card = 4} {b₁ b₂ : Bool}
    (hlK : (((secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) (tightCore Rd)).subgroupOf
      (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t))).subgroupOf
        (pSpan (restrictFamily (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t))
          (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t))))).map φ =
      memBar γ₁ h₁ b₁)
    (hlJ : (((secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) J).subgroupOf
      (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t))).subgroupOf
        (pSpan (restrictFamily (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t))
          (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t))))).map φ =
      memBar γ₂ h₂ b₂) :
    γ₁ = γ₂ ∨ Disjoint γ₂ γ₁ := by
  have h := TightLargeHypR.typeRFam hs.large
  have hzY := mem_layerY_of_isUniqueInvolution h hs.xMem_K hs.hz
  have htY := mem_layerY_of_isUniqueInvolution h hs.xMem_J hs.ht
  have hzb := isUniqueInvolution_secImg h hs.xMem_K hs.hz
  have htb := isUniqueInvolution_secImg h hs.xMem_J hs.ht
  have hK' : (secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) (tightCore Rd)).subgroupOf
      (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t)) ∈
      restrictFamily (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t))
        (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t)) :=
    ⟨_, secImg_mem hs.xMem_K, hKX, rfl⟩
  have hJ' : (secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) J).subgroupOf
      (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t)) ∈
      restrictFamily (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t))
        (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t)) :=
    ⟨_, secImg_mem hs.xMem_J, hJX, rfl⟩
  have hu := isUniqueInvolution_subgroupOf hzb hKX
  have hu' := isUniqueInvolution_subgroupOf htb hJX
  have h8K : Nat.card ↥((secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t)
      (tightCore Rd)).subgroupOf (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd)
        (z * t))) = 8 := by rw [hD.card _ hK']; norm_num
  have h8J : Nat.card ↥((secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) J).subgroupOf
      (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t))) = 8 := by
    rw [hD.card _ hJ']; norm_num
  have hzK := phi_map_eq_zBar φ hm hK' h8K hlK hu
  have hzJ := phi_map_eq_zBar φ hm hJ' h8J hlJ hu'
  have hcenZ := hs.mk_mul_mk_mem_center hzY htY
  have hcomm : ∀ x ∈ memBar γ₁ h₁ b₁, zBar γ₂ h₂ * x = x * zBar γ₂ h₂ := by
    intro x hx
    have hx' := hx
    rw [← hlK] at hx'
    obtain ⟨w, -, rfl⟩ := hx'
    have e1 : (zBar γ₁ h₁ * zBar γ₂ h₂) * φ w = φ w * (zBar γ₁ h₁ * zBar γ₂ h₂) := by
      rw [← hzK, ← hzJ, ← map_mul, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      apply Subtype.ext
      exact Subgroup.mem_center_iff.mp hcenZ _ |>.symm
    have e2 : zBar γ₁ h₁ * φ w = φ w * zBar γ₁ h₁ := AE.zBar_comm_memBar γ₁ h₁ b₁ _ hx
    have e3 : (zBar γ₁ h₁)⁻¹ = zBar γ₁ h₁ :=
      inv_eq_of_mul_eq_one_right (AE.zBar_mul_self γ₁ h₁)
    calc zBar γ₂ h₂ * φ w = (zBar γ₁ h₁)⁻¹ * ((zBar γ₁ h₁ * zBar γ₂ h₂) * φ w) := by group
      _ = (zBar γ₁ h₁)⁻¹ * (φ w * (zBar γ₁ h₁ * zBar γ₂ h₂)) := by rw [e1]
      _ = (zBar γ₁ h₁)⁻¹ * (zBar γ₁ h₁ * φ w) * zBar γ₂ h₂ := by rw [e2]; group
      _ = φ w * zBar γ₂ h₂ := by group
  by_cases he : γ₁ = γ₂
  · exact Or.inl he
  · exact Or.inr (AE.disjoint_of_zBar_comm (Ne.symm he) hcomm)

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
