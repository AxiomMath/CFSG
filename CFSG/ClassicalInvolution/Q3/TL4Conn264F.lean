module

public import CFSG.ClassicalInvolution.Q3.TL4Conn264E
public import CFSG.ClassicalInvolution.Q3.TL4SecIdE2B
public import CFSG.ClassicalInvolution.Q3.TL4Conn264D
public import CFSG.ClassicalInvolution.Q3.TL4Conn264M
public import CFSG.ClassicalInvolution.Q3.TL4Conn264O
public import CFSG.ClassicalInvolution.Q3.TL4SecIdE2AEC

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.T8 (XMem ne_of_mem_omegaNbr)
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin (pSpan ThmDHyp AEIdent AEIdentOn E8Struct)
open CFSG.ClassicalInvolution.Q3.AE (AEQ memBar)

theorem exists_xMem_of_mem_restrictFamily {G : Type} [Group G] {Ω : Set (Subgroup G)} {x : G}
    {Xb : Subgroup (SecQuot Ω x)} {M : Subgroup ↥Xb}
    (hM : M ∈ restrictFamily (secFam Ω x) Xb) :
    ∃ L : Subgroup G, XMem Ω x L ∧ ∃ _ : secImg Ω x L ≤ Xb, (secImg Ω x L).subgroupOf Xb = M := by
  obtain ⟨M', hM', hM'X, rfl⟩ := hM
  obtain ⟨L, hL, rfl⟩ := mem_secFam_iff.mp hM'
  exact ⟨L, hL, hM'X, rfl⟩

theorem exists_ne_zero_ne : ∀ v : Fin 3 → ZMod 2, ∃ w : Fin 3 → ZMod 2, w ≠ 0 ∧ w ≠ v := by
  decide

theorem eq_one_of_mem_center_of_e8 {G : Type} [Group G] [Finite G] {E : Subgroup G}
    (hE : E8Struct ⊤ E) {c : G} (hc : ∀ g : G, g * c = c * g) (hcE : c ∈ E) : c = 1 := by
  classical
  obtain ⟨e, he⟩ := exists_e8Basis hE.sq hE.card
  obtain ⟨v, rfl⟩ := exists_e8Coord_eq he hcE
  by_contra h1
  have hv : v ≠ 0 := fun hv => h1 (by rw [hv, e8Coord_zero])
  obtain ⟨w, hw0, hwv⟩ := exists_ne_zero_ne v
  obtain ⟨M, hM⟩ := SecIdE2.sl3Two_transitive w v hw0 hv
  obtain ⟨x, hx⟩ := e8Hom_surjective hE he M
  have h2 := conj_e8Coord_e8Hom hE he x v
  rw [hx, hM] at h2
  have h3 : (x : G) * e8Coord e v * (x : G)⁻¹ = e8Coord e v := by
    rw [hc (x : G), mul_inv_cancel_right]
  rw [h3] at h2
  exact hwv (e8Coord_injective he h2).symm

theorem fanoLines_exists_meet : ∀ ℓ ∈ AE.fanoLines, ∃ ℓ' ∈ AE.fanoLines, (ℓᶜ ∩ ℓ'ᶜ).card = 2 := by
  decide +kernel

theorem affinePlanes_exists_meet :
    ∀ α ∈ AE.affinePlanes, ∃ β ∈ AE.affinePlanes, (α ∩ β).card = 2 := by
  decide +kernel

theorem affinePlanes_exists_meet_compl : ∀ α ∈ AE.affinePlanes, ∀ γ ∈ AE.affinePlanes,
    Disjoint α γ → ∃ β ∈ AE.affinePlanes, (α ∩ β).card = 2 ∧ γ ∩ β = β \ (α ∩ β) := by
  decide +kernel

theorem false_of_disjoint_four {m : ℕ} (hm : m < 8) {α β : Finset (Fin m)} (hα : α.card = 4)
    (hβ : β.card = 4) (hd : Disjoint α β) : False := by
  have hc := Finset.card_union_of_disjoint hd
  have hle := Finset.card_le_univ (α ∪ β)
  rw [Fintype.card_fin, hc, hα, hβ] at hle
  omega

theorem secImg_J_le_secOrb {G : Type} [Group G] {Ω : Set (Subgroup G)} {K J : Subgroup G} {x : G}
    (hcj : SecConj264 Ω K J x) : secImg Ω x J ≤ secOrb Ω K x := by
  obtain ⟨g₀, hg₀⟩ := hcj
  rw [← hg₀]
  exact Vtx.conjSub_le_orbGrp _ ⟨g₀, by rw [omegaGen_secFam]; exact Subgroup.mem_top _⟩

section Cit3


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {Rd : Subgroup Y} {Sd : Sylow 2 Rd} {z : Y}
  {J : Subgroup Y} {S : Sylow 2 Y} {R T W : Subgroup Y} {t : Y}

theorem TightStd8R.false_of_subsingleton_secOrb (hs : TightStd8R 3 n Rd Sd z J S R T W t)
    (hcj : SecConj264 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) J (z * t))
    (h1 : ∀ L ∈ restrictFamily (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t))
      (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t)),
        ∀ L' ∈ restrictFamily (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t))
          (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t)), L = L') :
    False := by
  have hKX : secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) (tightCore Rd) ≤
      secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t) := Vtx.le_orbGrp _
  have hJX := secImg_J_le_secOrb hcj
  have e := h1 _ ⟨_, secImg_mem hs.xMem_K, hKX, rfl⟩ _ ⟨_, secImg_mem hs.xMem_J, hJX, rfl⟩
  rw [Subgroup.subgroupOf_inj, inf_eq_left.mpr hKX, inf_eq_left.mpr hJX] at e
  exact hs.secImg_J_mem_omegaNbr.2.1 e.symm

theorem TightStd8R.exists_central_secOrb (hs : TightStd8R 3 n Rd Sd z J S R T W t)
    (hcj : SecConj264 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) J (z * t)) :
    ∃ c : ↥(secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t)),
      c ≠ 1 ∧ ∀ g, g * c = c * g := by
  classical
  set Ω := CoreAssembly.conjClass (tightCore Rd) with hΩdef
  set K := tightCore Rd with hKdef
  have h := TightLargeHypR.typeRFam hs.large
  have hzY := mem_layerY_of_isUniqueInvolution h hs.xMem_K hs.hz
  have htY := mem_layerY_of_isUniqueInvolution h hs.xMem_J hs.ht
  have hzb := isUniqueInvolution_secImg h hs.xMem_K hs.hz
  have htb := isUniqueInvolution_secImg h hs.xMem_J hs.ht
  have hKX : secImg Ω (z * t) K ≤ secOrb Ω K (z * t) := Vtx.le_orbGrp _
  have hJX := secImg_J_le_secOrb hcj
  have hcen := hs.mk_mul_mk_mem_center hzY htY
  have habX : (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω (z * t))) ⟨z, hzY⟩ *
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω (z * t))) ⟨t, htY⟩ :
        SecQuot Ω (z * t)) ∈ secOrb Ω K (z * t) :=
    (secOrb Ω K (z * t)).mul_mem (hKX hzb.mem) (hJX htb.mem)
  have hzt : z * t = t * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hs.hyp hs.hz hs.hJ hs.ht
  have hztne : z ≠ t := ne_of_mem_omegaNbr hs.noTwins hs.hJ hs.hz hs.ht
  have hab1 : (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω (z * t))) ⟨z, hzY⟩ *
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω (z * t))) ⟨t, htY⟩ :
        SecQuot Ω (z * t)) ≠ 1 := by
    rw [← map_mul]
    intro h1
    have hmem := (QuotientGroup.eq_one_iff _).mp h1
    have hne1 : (⟨z, hzY⟩ * ⟨t, htY⟩ : ↥(layerY Ω (z * t))) ≠ 1 := by
      intro e
      apply hztne
      have e' : z * t = 1 := congrArg Subtype.val e
      calc z = z * t * t := by rw [mul_assoc, hs.ht.sq, mul_one]
        _ = t := by rw [e', one_mul]
    have hsq : (⟨z, hzY⟩ * ⟨t, htY⟩ : ↥(layerY Ω (z * t))) *
        (⟨z, hzY⟩ * ⟨t, htY⟩) = 1 := by
      apply Subtype.ext
      show z * t * (z * t) = 1
      calc z * t * (z * t) = z * (t * z) * t := by group
        _ = z * (z * t) * t := by rw [← hzt]
        _ = (z * z) * (t * t) := by group
        _ = 1 := by rw [hs.hz.sq, hs.ht.sq, mul_one]
    have hord : orderOf (⟨z, hzY⟩ * ⟨t, htY⟩ : ↥(layerY Ω (z * t))) = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact hsq) hne1
    have hpg : IsPGroup 2 ↥(Subgroup.zpowers (⟨z, hzY⟩ * ⟨t, htY⟩ : ↥(layerY Ω (z * t)))) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
    exact hne1 (eq_one_of_isPGroup_of_mem_odd
      (CFSG.ComponentClassification.OddCore.odd_card _) hmem hpg)
  exact ⟨⟨_, habX⟩, fun e => hab1 (congrArg Subtype.val e),
    fun g => Subtype.ext (Subgroup.mem_center_iff.mp hcen (g : SecQuot Ω (z * t)))⟩

theorem TightStd8R.false_of_e8_secOrb (hs : TightStd8R 3 n Rd Sd z J S R T W t)
    (hcj : SecConj264 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) J (z * t))
    {E : Subgroup ↥(secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t))}
    (hE8 : E8Struct ⊤ E) : False := by
  obtain ⟨c, hc1, hc⟩ := hs.exists_central_secOrb hcj
  exact hc1 (eq_one_of_mem_center_of_e8 hE8 hc
    (hE8.cent c (Subgroup.mem_top _) fun e _ => (hc e).symm))

theorem TightStd8R.false_of_meet_labels (hs : TightStd8R 3 n Rd Sd z J S R T W t)
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
    {γ₁ γ₂ β : Finset (Fin m)} {h₁ : γ₁.card = 4} {h₂ : γ₂.card = 4} (hβ : β.card = 4)
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
    (hc : (γ₁ ∩ β).card = 2) (hc₂ : γ₂ ∩ β = γ₁ ∩ β ∨ γ₂ ∩ β = β \ (γ₁ ∩ β))
    (h12 : memBar γ₁ h₁ b₁ ≤ Subgroup.normalizer (memBar γ₂ h₂ b₂ : Set (AEQ m)))
    (hlab : ∃ L ∈ restrictFamily (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t))
      (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t)),
        (L.subgroupOf (pSpan (restrictFamily
          (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t))
          (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t))))).map φ =
          memBar β hβ true) : False := by
  classical
  obtain ⟨p, q, hpq, hpqe⟩ := Finset.card_eq_two.mp hc
  have hpm : p ∈ γ₁ ∩ β := by rw [hpqe]; simp
  have hqm : q ∈ γ₁ ∩ β := by rw [hpqe]; simp
  have hp : p ∈ β := (Finset.mem_inter.mp hpm).2
  have hq : q ∈ β := (Finset.mem_inter.mp hqm).2
  have hsub : ({p, q} : Finset (Fin m)) ⊆ β := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hp
    · exact hq
  have hcard2 : (β \ {p, q}).card = 2 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, hβ, Finset.card_pair hpq]
  have hn : ∀ γ : Finset (Fin m), (γ ∩ β).card = 2 → ¬ β ⊆ γ := fun γ hγ hsub' => by
    rw [Finset.inter_eq_right.mpr hsub', hβ] at hγ
    omega
  have hc₂' : γ₂ ∩ β = {p, q} ∨ γ₂ ∩ β = β \ {p, q} := by
    rcases hc₂ with e | e
    · exact Or.inl (e.trans hpqe)
    · exact Or.inr (by rw [e, hpqe])
  have hn₂ : ¬ β ⊆ γ₂ := by
    refine hn γ₂ ?_
    rcases hc₂' with e | e
    · rw [e, Finset.card_pair hpq]
    · rw [e, hcard2]
  obtain ⟨v, hvβ, hv2, hvout, hvn⟩ := SecIdE2.exists_normalizing_memBar_pair hm hβ hp hq hpq
  obtain ⟨L', hL', hlL'⟩ := hlab
  obtain ⟨L, hL, hLX, rfl⟩ := exists_xMem_of_mem_restrictFamily hL'
  exact hs.false_of_three_labels hE hD hm φ hker hKX hJX hL hlK hlJ hlL' hvβ hv2
    (hvn γ₁ h₁ (Or.inl hpqe) b₁) (hvn γ₂ h₂ hc₂' b₂) h12 (hvout γ₁ h₁ b₁ (hn γ₁ hc))
    (hvout γ₂ h₂ b₂ hn₂)

theorem TightStd8R.false_of_aeIdent_secOrb (hs : TightStd8R 3 n Rd Sd z J S R T W t)
    (hE : MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W)
    (hcj : SecConj264 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) J (z * t))
    (hD : ThmDHyp 3 (restrictFamily (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t))
      (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t))))
    {m : ℕ} (hm : 6 ≤ m)
    (I : AEIdent (restrictFamily (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t))
      (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t))) m) : False := by
  classical
  have hKX : secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) (tightCore Rd) ≤
      secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t) := Vtx.le_orbGrp _
  have hJX := secImg_J_le_secOrb hcj
  obtain ⟨γ₁, h₁, b₁, hlK⟩ := I.label _ ⟨_, secImg_mem hs.xMem_K, hKX, rfl⟩
  obtain ⟨γ₂, h₂, b₂, hlJ⟩ := I.label _ ⟨_, secImg_mem hs.xMem_J, hJX, rfl⟩
  rcases hs.labels_eq_or_disjoint hD (by omega) I.φ hKX hJX hlK hlJ with e | hd
  · subst e
    have hcard : 2 ≤ (γ₁ᶜ).card := by
      rw [Finset.card_compl, Fintype.card_fin, h₁]
      omega
    obtain ⟨p, q, β, hβ, -, -, hpq, hγβ, -, -, -⟩ :=
      exists_quad (by omega : 2 ≤ γ₁.card) hcard disjoint_compl_right
    exact hs.false_of_meet_labels hE hD (by omega) I.φ I.ker_le hKX hJX hβ hlK hlJ
      (by rw [hγβ, Finset.card_pair hpq]) (Or.inl rfl) (memBar_le_normalizer_twin h₁ h₂ b₁ b₂)
      (I.label_surj β hβ true)
  · obtain ⟨p, q, β, hβ, -, -, hpq, h1, h2, -, -⟩ :=
      exists_quad (by omega : 2 ≤ γ₁.card) (by omega : 2 ≤ γ₂.card) hd.symm
    exact hs.false_of_meet_labels hE hD (by omega) I.φ I.ker_le hKX hJX hβ hlK hlJ
      (by rw [h1, Finset.card_pair hpq]) (Or.inr (by rw [h2, h1]))
      (le_normalizer_of_comm (AE.comm_memBar_of_disjoint hd.symm b₁ b₂))
      (I.label_surj β hβ true)

theorem TightStd8R.false_of_e64_secOrb (hs : TightStd8R 3 n Rd Sd z J S R T W t)
    (hE : MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W)
    (hcj : SecConj264 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) J (z * t))
    (hD : ThmDHyp 3 (restrictFamily (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t))
      (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t))))
    (I : AEIdentOn (restrictFamily (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t))
      (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t))) 7 AE.e64Sets
        AE.e64Sub) : False := by
  classical
  have hKX : secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) (tightCore Rd) ≤
      secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t) := Vtx.le_orbGrp _
  have hJX := secImg_J_le_secOrb hcj
  obtain ⟨γ₁, hγ₁, h₁, b₁, hlK⟩ := I.label _ ⟨_, secImg_mem hs.xMem_K, hKX, rfl⟩
  obtain ⟨γ₂, -, h₂, b₂, hlJ⟩ := I.label _ ⟨_, secImg_mem hs.xMem_J, hJX, rfl⟩
  rcases hs.labels_eq_or_disjoint hD (by norm_num) I.φ hKX hJX hlK hlJ with e | hd
  · subst e
    obtain ⟨ℓ, hℓ, rfl⟩ := hγ₁
    obtain ⟨ℓ', hℓ', hc⟩ := fanoLines_exists_meet ℓ hℓ
    have hβm : ℓ'ᶜ ∈ AE.e64Sets := ⟨ℓ', hℓ', rfl⟩
    have hβ := SecIdE2.card_of_mem_e64Sets hβm
    exact hs.false_of_meet_labels hE hD (by norm_num) I.φ I.ker_le hKX hJX hβ hlK hlJ hc
      (Or.inl rfl) (memBar_le_normalizer_twin h₁ h₂ b₁ b₂) (I.label_surj _ hβm hβ true)
  · exact false_of_disjoint_four (by norm_num) h₂ h₁ hd

theorem TightStd8R.false_of_e29_secOrb (hs : TightStd8R 3 n Rd Sd z J S R T W t)
    (hE : MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W)
    (hcj : SecConj264 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) J (z * t))
    (hD : ThmDHyp 3 (restrictFamily (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t))
      (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t))))
    (I : AEIdentOn (restrictFamily (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t))
      (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t))) 8 AE.e29Sets
        AE.e29Sub) : False := by
  classical
  have hKX : secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) (tightCore Rd) ≤
      secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t) := Vtx.le_orbGrp _
  have hJX := secImg_J_le_secOrb hcj
  obtain ⟨γ₁, hγ₁, h₁, b₁, hlK⟩ := I.label _ ⟨_, secImg_mem hs.xMem_K, hKX, rfl⟩
  obtain ⟨γ₂, hγ₂, h₂, b₂, hlJ⟩ := I.label _ ⟨_, secImg_mem hs.xMem_J, hJX, rfl⟩
  rcases hs.labels_eq_or_disjoint hD (by norm_num) I.φ hKX hJX hlK hlJ with e | hd
  · subst e
    obtain ⟨β, hβm, hc⟩ := affinePlanes_exists_meet γ₁ hγ₁
    have hβ := SecIdE2.card_of_mem_e29Sets hβm
    exact hs.false_of_meet_labels hE hD (by norm_num) I.φ I.ker_le hKX hJX hβ hlK hlJ hc
      (Or.inl rfl) (memBar_le_normalizer_twin h₁ h₂ b₁ b₂) (I.label_surj β hβm hβ true)
  · obtain ⟨β, hβm, hc, hc₂⟩ := affinePlanes_exists_meet_compl γ₁ hγ₁ γ₂ hγ₂ hd.symm
    have hβ := SecIdE2.card_of_mem_e29Sets hβm
    exact hs.false_of_meet_labels hE hD (by norm_num) I.φ I.ker_le hKX hJX hβ hlK hlJ hc
      (Or.inr hc₂) (le_normalizer_of_comm (AE.comm_memBar_of_disjoint hd.symm b₁ b₂))
      (I.label_surj β hβm hβ true)

theorem tightC264E2_of (h4 : Thm4RBelow 3 n) (hLC : TightLambdaCommR 3 n) : TightC264E2 n := by
  intro hP Y _ _ Rd Sd z J S R T W t hs hΛp hE hcj hO2
  have hD := hs.thmDHyp_secOrb h4 hO2
  rcases hs.thmDConcl_secOrb hP h4 hO2 with h1 | ⟨V, hW1⟩ | ⟨E, hE8⟩ | hI | ⟨m, hm, hI⟩ | hI
  · exact (hs.false_of_subsingleton_secOrb hcj h1).elim
  · exact Or.inl (hs.c264One_of_wSet_secOrb h4 hE hcj hD hW1)
  · exact (hs.false_of_e8_secOrb hcj hE8).elim
  · obtain ⟨I⟩ := hI
    exact (hs.false_of_e64_secOrb hE hcj hD I).elim
  · obtain ⟨I⟩ := hI
    rcases (by omega : m = 5 ∨ 6 ≤ m) with rfl | hm6
    · exact (hs.false_of_ae5_secOrb hLC hΛp hE hcj hD I).elim
    · exact (hs.false_of_aeIdent_secOrb hE hcj hD hm6 I).elim
  · obtain ⟨I⟩ := hI
    exact (hs.false_of_e29_secOrb hE hcj hD I).elim

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
