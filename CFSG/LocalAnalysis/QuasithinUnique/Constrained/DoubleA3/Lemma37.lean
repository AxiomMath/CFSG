module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.R37Reentry
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.R37Dihedral
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.FinalFacts
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Claim1Assembly
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma35
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115CharTwoTools
import Mathlib.Tactic.Group
public import Certificates.Certificate1
public import Certificates.Certificate2
public import CFSG.Sporadic.Schreier.J4SSylow
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.GammaLemmas

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G]

theorem mem_conjClass_of_conj {z₂ n g : G} (h : g * n * g⁻¹ ∈ conjClass z₂) : n ∈ conjClass z₂ := by
  have h1 := conj_mem_conjClass h g
  have e : g⁻¹ * (g * n * g⁻¹) * g = n := by group
  rw [e] at h1
  exact h1

theorem involution_mem_conjClass {K : Subgroup G} {z₁ z₂ s : G}
    (e : ↥K ≃* alternatingGroup (Fin 6)) (hz₁K : z₁ ∈ K) (hz₁1 : z₁ ≠ 1) (hz₁2 : z₁ * z₁ = 1)
    (hz₂ : z₂ = s⁻¹ * z₁ * s) {y : G} (hy : y ∈ K) (hy2 : y * y = 1) (hy1 : y ≠ 1) :
    y ∈ conjClass z₂ := by
  let a : alternatingGroup (Fin 6) := e ⟨y, hy⟩
  let b : alternatingGroup (Fin 6) := e ⟨z₁, hz₁K⟩
  have ha1 : a ≠ 1 := by
    intro h
    have : (⟨y, hy⟩ : K) = 1 := e.injective (by simpa [a] using h)
    exact hy1 (congrArg Subtype.val this)
  have ha2 : a * a = 1 := by
    have : (⟨y, hy⟩ : K) * ⟨y, hy⟩ = 1 := Subtype.ext hy2
    show e ⟨y, hy⟩ * e ⟨y, hy⟩ = 1
    rw [← map_mul, this, map_one]
  have hb1 : b ≠ 1 := by
    intro h
    have : (⟨z₁, hz₁K⟩ : K) = 1 := e.injective (by simpa [b] using h)
    exact hz₁1 (congrArg Subtype.val this)
  have hb2 : b * b = 1 := by
    have : (⟨z₁, hz₁K⟩ : K) * ⟨z₁, hz₁K⟩ = 1 := Subtype.ext hz₁2
    show e ⟨z₁, hz₁K⟩ * e ⟨z₁, hz₁K⟩ = 1
    rw [← map_mul, this, map_one]
  obtain ⟨g, hg⟩ := alt6_involutions_conj b a hb1 hb2 ha1 ha2
  have hk : (e.symm g)⁻¹ * (⟨z₁, hz₁K⟩ : K) * e.symm g = ⟨y, hy⟩ := by
    apply e.injective
    simpa [a, b] using hg
  have hk' : ((e.symm g : K) : G)⁻¹ * z₁ * (e.symm g : K) = y := by
    have := congrArg Subtype.val hk
    simpa using this
  refine ⟨s⁻¹ * (e.symm g : K), ?_⟩
  rw [← hk', hz₂]
  group

section Config

variable [Finite G] {T M H S L K : Subgroup G} {s x z₁ z₂ : G}

theorem A3A3K.z_not_mem_conjClass (hD : AppC.C56DoubleA3) (h27_1 : Lemma2_4_27_1A3)
    (hK : A3A3K T M H S L s x z₁ z₂ K) : z₁ * z₂ ∉ conjClass z₂ := by
  rintro ⟨g, hg⟩
  have hcs := hK.cs
  have hB := basic31 hD h27_1 hK.toA3A3
  have hzT := z_central hB hK.toA3A3x
  have hz1 : z₁ * z₂ ≠ 1 := hK.toA3A3x.z_ne
  have hz2 : (z₁ * z₂) ^ 2 = 1 := hK.toA3A3x.sq_z
  have hTc : T ≤ centralizerElem (z₁ * z₂) := fun t ht =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hzT.2 t ht)
  have hpc : pCoreOf 2 (centralizerElem (z₁ * z₂)) ≠ ⊥ := pCoreOf_centralizerElem_ne_bot hz1 hz2
  have hchar : CharTwo (centralizerElem (z₁ * z₂)) :=
    charTwo_of_isSylowTwoOf_le_of_pCore_ne_bot hcs.setting.qtke.2.1 hcs.setting.sylow hTc hpc
  have hmap : (centralizerElem (z₁ * z₂)).map (MulAut.conj g).toMonoidHom = centralizerElem z₂ := by
    ext y
    rw [Subgroup.mem_map_equiv]
    show g⁻¹ * y * g ∈ centralizerElem (z₁ * z₂) ↔ y ∈ centralizerElem z₂
    unfold centralizerElem
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff, hg]
    constructor
    · intro h
      have h1 : g⁻¹ * y * g * (g⁻¹ * z₂ * g) = g⁻¹ * z₂ * g * (g⁻¹ * y * g) := h
      have h2 : y * z₂ = z₂ * y := by
        calc y * z₂ = g * (g⁻¹ * y * g * (g⁻¹ * z₂ * g)) * g⁻¹ := by group
          _ = g * (g⁻¹ * z₂ * g * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
          _ = z₂ * y := by group
      exact h2
    · intro h
      calc g⁻¹ * y * g * (g⁻¹ * z₂ * g) = g⁻¹ * (y * z₂) * g := by group
        _ = g⁻¹ * (z₂ * y) * g := by rw [h]
        _ = g⁻¹ * z₂ * g * (g⁻¹ * y * g) := by group
  have h1 := Ch1.charTwo_map_mulEquiv (MulAut.conj g) hchar
  rw [hmap] at h1
  exact not_isComponentIn_of_charTwo h1 K hK.K_comp

section Core

variable (hD : AppC.C56DoubleA3) (h27_1 : Lemma2_4_27_1A3) (hSA : ConstrainedSetupAt)
  (hlin : Lin2BlockExcluded) (ha5 : A5BlockExcluded) (ha3 : SingleA3Excluded)
  (h34 : Lemma2_4_34_used) (hK : A3A3K T M H S L s x z₁ z₂ K)
include hD h27_1 hSA hlin ha5 ha3 h34 hK

theorem A3A3K.mixed_not_mem_conjClass
    (hbot : (baum S ⊓ K) ⊓ conjR (baum S ⊓ K) s = ⊥)
    (hcomm : ∀ a ∈ baum S ⊓ K, ∀ b ∈ conjR (baum S ⊓ K) s, a * b = b * a)
    (hR64 : Nat.card (baum S) = 64) {a b : G}
    (ha : a ∈ blockU L ∨ a ∈ conjR (blockU L) x) (hb : b ∈ blockU2 L s) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) : a * b ∉ conjClass z₂ := by
  have hcs := hK.cs
  have hB := basic31 hD h27_1 hK.toA3A3
  obtain ⟨e⟩ := hK.nonempty_alt6 h34
  have hz₁K : z₁ ∈ K := hK.z₁_mem_K
  have hz₁1 : z₁ ≠ 1 := hK.z₁_ne
  have hz₁2 : z₁ * z₁ = 1 := by simpa [pow_two] using hK.toA3A3x.sq₁
  have hcl : ∀ y ∈ K, y * y = 1 → y ≠ 1 → y ∈ conjClass z₂ := fun y hy h2 h1 =>
    involution_mem_conjClass e hz₁K hz₁1 hz₁2 hK.z₂_def hy h2 h1
  have hUK : blockU L ≤ K := hK.isA4.le.trans hK.L_le_K
  have hsq : ∀ u ∈ blockU L, u * u = 1 := fun u hu => by
    simpa [pow_two] using hK.isA4.sq_U u hu
  have hUcl : ∀ p ∈ blockU L, p ≠ 1 → p ∈ conjClass z₂ := fun p hp hp1 =>
    hcl p (hUK hp) (hsq p hp) hp1
  have hne1 : ∀ (g p : G), g * p * g⁻¹ = 1 → p = 1 := fun g p h => by
    have : p = g⁻¹ * (g * p * g⁻¹) * g := by group
    rw [this, h]
    group
  have hUxcl : ∀ p ∈ conjR (blockU L) x, p ≠ 1 → p ∈ conjClass z₂ := fun p hp hp1 =>
    mem_conjClass_of_conj (g := x) (hUcl _ (mem_conjR.mp hp) (fun h => hp1 (hne1 x p h)))
  have hU2cl : ∀ n ∈ blockU2 L s, n ≠ 1 → n ∈ conjClass z₂ := fun n hn hn1 =>
    mem_conjClass_of_conj (g := s) (hUcl _ (mem_conjR.mp hn) (fun h => hn1 (hne1 s n h)))
  have hzT := z_central hB hK.toA3A3x
  have hz₁U : z₁ ∈ blockU L := hK.toA3A3x.z₁_mem.1
  have hz₂U : z₂ ∈ blockU2 L s := hK.toA3A3x.z₂_mem.1
  have hzZ := hK.z_not_mem_conjClass hD h27_1
  have hinf : blockU L ⊓ blockU2 L s = ⊥ := hK.isA4.inf_eq_bot hK.isA4s hK.comm_elem
  rcases ha with haU | haUx
  ·
    have hz : z₁ * z₂ ∈ blockU L ⊔ blockU2 L s := mul_mem (mem_sup_left hz₁U) (mem_sup_right hz₂U)
    have hzU : z₁ * z₂ ∉ blockU L := by
      intro h
      have h2 : z₂ ∈ blockU L := by
        have := mul_mem (inv_mem hz₁U) h
        simpa using this
      have : z₂ ∈ blockU L ⊓ blockU2 L s := ⟨h2, hz₂U⟩
      rw [hinf] at this
      exact hK.toA3A3x.z₂_ne (Subgroup.mem_bot.mp this)
    have hzU₂ : z₁ * z₂ ∉ blockU2 L s := by
      intro h
      have h2 : z₁ ∈ blockU2 L s := by
        have := mul_mem h (inv_mem hz₂U)
        simpa using this
      have : z₁ ∈ blockU L ⊓ blockU2 L s := ⟨hz₁U, h2⟩
      rw [hinf] at this
      exact hz₁1 (Subgroup.mem_bot.mp this)
    have haU' : a ∈ blockU L := haU
    exact no_mixed_mem_conjClass hK.isA4 hK.isA4s hK.comm_elem hz hzU hzU₂ hzZ le_sup_left
      le_sup_right hK.isA4.card_U hK.isA4s.card_U hinf hUcl hU2cl a haU' b hb ha1 hb1
  ·
    obtain ⟨L₁, L₂, U₁, U₂, s', h₁, h₂, hc, hU, hs'T, hU₂⟩ :=
      hK.exists_blocks_A1 hD h27_1 hSA hlin ha5 ha3 hbot hcomm hR64
    have hinf' : U₁ ⊓ U₂ = ⊥ := h₁.inf_eq_bot h₂ hc
    have hz : z₁ * z₂ ∈ U₁ ⊔ U₂ := by rw [hU]; exact hK.z_mem_blockA1
    have hzs : s' * (z₁ * z₂) * s'⁻¹ = z₁ * z₂ := by
      have := Subgroup.mem_centralizer_iff.mp hzT.2 s' hs'T
      rw [this]
      group
    have hz1' : z₁ * z₂ ≠ 1 := hK.toA3A3x.z_ne
    have hzU₁ : z₁ * z₂ ∉ U₁ := by
      intro h
      have h2 : z₁ * z₂ ∈ U₂ := by
        rw [hU₂, mem_conjR, hzs]
        exact h
      have : z₁ * z₂ ∈ U₁ ⊓ U₂ := ⟨h, h2⟩
      rw [hinf'] at this
      exact hz1' (Subgroup.mem_bot.mp this)
    have hzU₂' : z₁ * z₂ ∉ U₂ := by
      intro h
      have h2 : z₁ * z₂ ∈ U₁ := by
        have h3 : s' * (z₁ * z₂) * s'⁻¹ ∈ U₁ := by rw [hU₂] at h; exact mem_conjR.mp h
        rw [hzs] at h3
        exact h3
      have : z₁ * z₂ ∈ U₁ ⊓ U₂ := ⟨h2, h⟩
      rw [hinf'] at this
      exact hz1' (Subgroup.mem_bot.mp this)
    have hUx := hK.blockUx_le_rK hD h27_1
    have hU2R := hK.blockU2_le_rKs
    have hPN : conjR (blockU L) x ⊓ blockU2 L s = ⊥ := by
      rw [eq_bot_iff]
      intro g hg
      have : g ∈ (baum S ⊓ K) ⊓ conjR (baum S ⊓ K) s := ⟨hUx hg.1, hU2R hg.2⟩
      rw [hbot] at this
      exact this
    have hP : conjR (blockU L) x ≤ U₁ ⊔ U₂ := by rw [hU]; exact le_sup_right
    have hN : blockU2 L s ≤ U₁ ⊔ U₂ := by rw [hU]; exact le_sup_left
    exact no_mixed_mem_conjClass h₁ h₂ hc hz hzU₁ hzU₂' hzZ hP hN (hK.isA4.conj x).card_U
      hK.isA4s.card_U hPN hUxcl hU2cl a haUx b hb ha1 hb1

end Core

end Config


theorem lemma2_4_37_used_of_36
    (hD : AppC.C56DoubleA3) (h27_1 : Lemma2_4_27_1A3)
    (hSA : ConstrainedSetupAt) (hlin : Lin2BlockExcluded) (ha5 : A5BlockExcluded)
    (ha3 : SingleA3Excluded) (h34 : Lemma2_4_34_used) (h36 : Lemma2_4_36) : Lemma2_4_37_used := by
  intro G _ _ T M H S L s x z₁ z₂ K hK y hy hyR
  obtain ⟨⟨⟨-, ⟨f⟩⟩, hRsup, hbot, hcomm⟩, -, -, hT256⟩ := h36 G T M H S L s x z₁ z₂ K hK
  have hcs := hK.cs
  have hB := basic31 hD h27_1 hK.toA3A3
  have hR64 : Nat.card (baum S) = 64 := by
    have h1 := hB.card_T
    norm_num at hT256
    omega
  have hz₂2 : z₂ * z₂ = 1 := by simpa [pow_two] using hK.toA3A3x.sq₂
  have hy2 : y * y = 1 := by
    obtain ⟨g, hg⟩ := hy
    rw [hg]
    calc g⁻¹ * z₂ * g * (g⁻¹ * z₂ * g) = g⁻¹ * (z₂ * z₂) * g := by group
      _ = 1 := by rw [hz₂2]; group
  have hy1 : y ≠ 1 := by
    obtain ⟨g, hg⟩ := hy
    intro h
    apply hK.toA3A3x.z₂_ne
    have : z₂ = g * (g⁻¹ * z₂ * g) * g⁻¹ := by group
    rw [this, ← hg, h]
    group
  obtain ⟨a, ha, b, hb, hyab⟩ :=
    exists_mul_of_mem_sup_of_commute hcomm (by rw [← hRsup]; exact hyR)
  by_cases ha1 : a = 1
  · right
    rw [hyab, ha1, one_mul]
    exact hb
  by_cases hb1 : b = 1
  · left
    rw [hyab, hb1, mul_one]
    exact ha
  exfalso
  have hab : a * b = b * a := hcomm a ha b hb
  have hab2 : (a * a) * (b * b) = 1 := by
    calc a * a * (b * b) = a * (a * b) * b := by group
      _ = a * (b * a) * b := by rw [hab]
      _ = (a * b) * (a * b) := by group
      _ = y * y := by rw [hyab]
      _ = 1 := hy2
  have haa : a * a = 1 := by
    have hmem2 : a * a ∈ conjR (baum S ⊓ K) s := by
      have : a * a = (b * b)⁻¹ := eq_inv_of_mul_eq_one_left hab2
      rw [this]
      exact inv_mem (mul_mem hb hb)
    have : a * a ∈ (baum S ⊓ K) ⊓ conjR (baum S ⊓ K) s := ⟨mul_mem ha ha, hmem2⟩
    rw [hbot] at this
    exact this
  have hbb : b * b = 1 := by
    rw [haa, one_mul] at hab2
    exact hab2
  have hUK : blockU L ≤ baum S ⊓ K :=
    le_inf (blockU_le_baum hcs hK.a3) (hK.isA4.le.trans hK.L_le_K)
  have hUx := hK.blockUx_le_rK hD h27_1
  have hUne : blockU L ≠ conjR (blockU L) x := by
    intro h
    apply hK.x_good
    rw [← h]
    intro u hu
    exact Subgroup.mem_centralizer_iff.mpr fun v hv => hK.isA4.comm_U v hv u hu
  have hsqU : ∀ u ∈ blockU L, u * u = 1 := fun u hu => by
    simpa [pow_two] using hK.isA4.sq_U u hu
  have hsqUx : ∀ u ∈ conjR (blockU L) x, u * u = 1 := fun u hu => by
    simpa [pow_two] using (hK.isA4.conj x).sq_U u hu
  have hcover : ∀ c ∈ baum S ⊓ K, c * c = 1 → c ∈ blockU L ∨ c ∈ conjR (blockU L) x :=
    fun c hc hc2 => klein_cover f hUK hUx hK.isA4.card_U (hK.isA4.conj x).card_U hsqU hsqUx hUne
      hc hc2
  have hatype := hcover a ha haa
  have hsb : s * b * s⁻¹ ∈ baum S ⊓ K := mem_conjR.mp hb
  have hsb2 : (s * b * s⁻¹) * (s * b * s⁻¹) = 1 := by
    calc (s * b * s⁻¹) * (s * b * s⁻¹) = s * (b * b) * s⁻¹ := by group
      _ = 1 := by rw [hbb]; group
  have hbtype := hcover _ hsb hsb2
  have hne1 : ∀ (g p : G), g * p * g⁻¹ ≠ 1 → p ≠ 1 := fun g p h hp => h (by rw [hp]; group)
  have hne1' : ∀ (g p : G), p ≠ 1 → g * p * g⁻¹ ≠ 1 := fun g p hp h => hp (by
    have : p = g⁻¹ * (g * p * g⁻¹) * g := by group
    rw [this, h]
    group)
  have hmixed : ∀ a b : G, (a ∈ blockU L ∨ a ∈ conjR (blockU L) x) → b ∈ blockU2 L s → a ≠ 1 →
      b ≠ 1 → a * b ∉ conjClass z₂ := fun a b =>
    hK.mixed_not_mem_conjClass hD h27_1 hSA hlin ha5 ha3 h34 hbot hcomm hR64
  rcases hbtype with hbU | hbUx
  ·
    have hb' : b ∈ blockU2 L s := mem_conjR.mpr hbU
    exact hmixed a b hatype hb' ha1 hb1 (hyab ▸ hy)
  ·
    have hs : s ∈ T := hcs.le_T hK.s_mem
    have hx : x ∈ T := hK.x_mem
    have hxx := hK.sq_x_mem hD h27_1
    have hUnorm := baum_le_normalizer_blockU hcs hK.a3
    have hv : x * (s * b * s⁻¹) * x⁻¹ ∈ blockU L := mem_conjR.mp hbUx
    rcases hatype with haU | haUx
    ·
      have hc'' : s * x⁻¹ * s⁻¹ * x ∈ baum S := by
        have := hK.comm_mod_baum hD h27_1 s⁻¹ (inv_mem hs) x (hx)
        simpa using this
      have hu₁ : x⁻¹ * (s * b * s⁻¹) * x ∈ blockU L := by
        have e : x⁻¹ * (s * b * s⁻¹) * x =
            (x * x)⁻¹ * (x * (s * b * s⁻¹) * x⁻¹) * (x * x) := by group
        rw [e]
        have h1 := (Subgroup.mem_normalizer_iff.mp (hUnorm (inv_mem hxx)) _).mp hv
        simpa using h1
      have hb'' : x⁻¹ * b * x ∈ blockU2 L s := by
        show x⁻¹ * b * x ∈ conjR (blockU L) s
        rw [mem_conjR]
        have e : s * (x⁻¹ * b * x) * s⁻¹ =
            (s * x⁻¹ * s⁻¹ * x) * (x⁻¹ * (s * b * s⁻¹) * x) * (s * x⁻¹ * s⁻¹ * x)⁻¹ := by group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (hUnorm hc'') _).mp hu₁
      have ha'' : x⁻¹ * a * x ∈ conjR (blockU L) x := by
        rw [mem_conjR]
        have : x * (x⁻¹ * a * x) * x⁻¹ = a := by group
        rw [this]
        exact haU
      have hyc : (x⁻¹ * a * x) * (x⁻¹ * b * x) ∈ conjClass z₂ := by
        have h1 := conj_mem_conjClass hy x
        have e : x⁻¹ * y * x = (x⁻¹ * a * x) * (x⁻¹ * b * x) := by rw [hyab]; group
        rw [e] at h1
        exact h1
      have ha1' : x⁻¹ * a * x ≠ 1 := by
        have := hne1' x⁻¹ a ha1
        simpa using this
      have hb1' : x⁻¹ * b * x ≠ 1 := by
        have := hne1' x⁻¹ b hb1
        simpa using this
      exact hmixed _ _ (Or.inr ha'') hb'' ha1' hb1' hyc
    ·
      have hc' : s * x * s⁻¹ * x⁻¹ ∈ baum S := by
        have := hK.comm_mod_baum hD h27_1 s⁻¹ (inv_mem hs) x⁻¹ (inv_mem hx)
        simpa using this
      have hb' : x * b * x⁻¹ ∈ blockU2 L s := by
        show x * b * x⁻¹ ∈ conjR (blockU L) s
        rw [mem_conjR]
        have e : s * (x * b * x⁻¹) * s⁻¹ =
            (s * x * s⁻¹ * x⁻¹) * (x * (s * b * s⁻¹) * x⁻¹) * (s * x * s⁻¹ * x⁻¹)⁻¹ := by group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (hUnorm hc') _).mp hv
      have ha' : x * a * x⁻¹ ∈ blockU L := mem_conjR.mp haUx
      have hyc : (x * a * x⁻¹) * (x * b * x⁻¹) ∈ conjClass z₂ := by
        have h1 := conj_mem_conjClass hy x⁻¹
        have e : x⁻¹⁻¹ * y * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by rw [hyab]; group
        rw [e] at h1
        exact h1
      exact hmixed _ _ (Or.inl ha') hb' (hne1' x a ha1) (hne1' x b hb1) hyc

end CFSG.QuasithinUnique.DoubleA3
