module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBSub6
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBIdx4
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBSub5

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42 CFSG.ComponentClassification.J2Cover CFSG.Sporadic.Schreier
open scoped commutatorElement

namespace EndB

theorem vComm_spec : (∀ i < 128, ∀ j < 128, ci vT vI i j ∈ vComm) ∧
    ∀ c ∈ vComm, ∃ i < 128, ∃ j < 128, ci vT vI i j = c := by
  refine ⟨fun i hi j hj => List.mem_dedup.mpr (List.mem_map.mpr ⟨(i, j),
    List.mem_product.mpr ⟨List.mem_range.mpr hi, List.mem_range.mpr hj⟩, rfl⟩), fun c hc => ?_⟩
  obtain ⟨⟨i, j⟩, hp, rfl⟩ := List.mem_map.mp (List.mem_dedup.mp hc)
  obtain ⟨hi, hj⟩ := List.mem_product.mp hp
  exact ⟨i, List.mem_range.mp hi, j, List.mem_range.mp hj, rfl⟩

namespace IdxModel

variable {G : Type*} [Group G] {e' : ℕ → G}
  (h' : IdxModel 128 e' vT vI 0)
include h'

theorem mem_iv_iff {x : G} : x ∈ cModZ h'.sub ↔ ∃ i ∈ ivList, e' i = x := by
  obtain ⟨-, hcen, hz, hcomm, hiv, hivlt, -⟩ := vIndex_facts
  exact h'.mem_cModZ_iff vComm_spec.1 vComm_spec.2 hcomm (by norm_num) hz hcen hivlt hiv

theorem card_iv : Nat.card (cModZ h'.sub) = 32 := by
  classical
  obtain ⟨-, -, -, -, -, hivlt, hnd, -⟩ := vIndex_facts
  have hbij : Function.Bijective (fun i : {i : ℕ // i ∈ ivList ∧ (fun _ => true) i = true} =>
      (⟨e' i.1, (h'.mem_iv_iff).mpr ⟨i.1, i.2.1, rfl⟩⟩ : ↥(cModZ h'.sub))) := by
    refine ⟨fun i j hij => Subtype.ext (h'.inj _ (hivlt _ i.2.1) _ (hivlt _ j.2.1)
      (congrArg Subtype.val hij)), ?_⟩
    rintro ⟨x, hx⟩
    obtain ⟨i, hi, rfl⟩ := (h'.mem_iv_iff).mp hx
    exact ⟨⟨i, hi, rfl⟩, rfl⟩
  rw [← Nat.card_eq_of_bijective _ hbij, card_subtype_mem_countP hnd, List.countP_true]
  rfl

theorem eq_of_comm_iv {x : G} (hx : x ∈ h'.sub) (hxc : ∀ l ∈ ivList, x * e' l = e' l * x) :
    x = 1 ∨ x = e' 1 := by
  obtain ⟨-, -, -, -, -, hivlt, -, hciv, -⟩ := vIndex_facts
  exact h'.centralizer_idx hivlt hciv hx hxc

theorem card_sigma : Nat.card {a : Fin 4 → ↥(cModZ h'.sub) //
    SigRel (e' 1) sqPat cmPat (fun k => (a k : G))} = 1920 := by
  obtain ⟨-, -, -, -, -, hivlt, hnd, -, hsig, -⟩ := vIndex_facts
  rw [h'.card_sig hivlt (fun x => h'.mem_iv_iff) (by norm_num) ivSq
    (fun k i hi => (List.mem_filter.mp hi).1) (fun k => hnd.filter _)
    (fun k i hi hsq => List.mem_filter.mpr ⟨hi, beq_iff_eq.mpr hsq⟩), hsig]

theorem closure_eq_iv [Finite G] {a : Fin 4 → G} (ha : ∀ k, a k ∈ cModZ h'.sub)
    (hsig : SigRel (e' 1) sqPat cmPat a) : closure (Set.range a) = cModZ h'.sub := by
  refine closure_eq_of_sigRel h'.card_iv ha hsig ?_
  have h01 : ⁅a 0, a 1⁆ = e' 1 := by simpa [cmPat] using hsig.2.1 0 1
  rw [← h01, commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem (subset_closure ⟨0, rfl⟩) (subset_closure ⟨1, rfl⟩))
    (inv_mem (subset_closure ⟨0, rfl⟩))) (inv_mem (subset_closure ⟨1, rfl⟩))

theorem card_centralizer_ge [Finite G] {W₁ : Subgroup G} (hW₁ : IsPGroup 2 W₁)
    (hcard : 1024 ≤ Nat.card W₁) (hn : ∀ g ∈ W₁, ∀ x ∈ h'.sub, g * x * g⁻¹ ∈ h'.sub)
    (hz : ∀ g ∈ W₁, g * e' 1 * g⁻¹ = e' 1) :
    8 ≤ Nat.card ↥((centralizer (cModZ h'.sub : Set G)).subgroupOf W₁) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnV := conj_mem_cModZ hn
  let Sg := {a : Fin 4 → ↥(cModZ h'.sub) // SigRel (e' 1) sqPat cmPat (fun k => (a k : G))}
  let act : MulAction ↥W₁ Sg :=
    { smul := fun g a => ⟨fun k => ⟨(g : G) * a.1 k * (g : G)⁻¹, hnV g g.2 _ (a.1 k).2⟩, by
        have := SigRel.map (f := (MulAut.conj (g : G)).toMonoidHom) (MulAut.conj (g : G)).injective
          a.2
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hz g g.2] at this
        exact this⟩
      one_smul := fun a => Subtype.ext (funext fun k => Subtype.ext (by
        change ((1 : ↥W₁) : G) * a.1 k * ((1 : ↥W₁) : G)⁻¹ = a.1 k
        simp))
      mul_smul := fun g₁ g₂ a => Subtype.ext (funext fun k => Subtype.ext (by
        change ((g₁ * g₂ : ↥W₁) : G) * a.1 k * ((g₁ * g₂ : ↥W₁) : G)⁻¹ =
          (g₁ : G) * ((g₂ : G) * a.1 k * (g₂ : G)⁻¹) * (g₁ : G)⁻¹
        simp only [Subgroup.coe_mul]
        group)) }
  have hstab : ∀ a : Sg, MulAction.stabilizer ↥W₁ a =
      (centralizer (cModZ h'.sub : Set G)).subgroupOf W₁ := by
    intro a
    ext g
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, mem_centralizer_iff]
    constructor
    · intro hg x hx
      have hfix : ∀ k, (g : G) * a.1 k * (g : G)⁻¹ = a.1 k := fun k =>
        congrArg Subtype.val (congrFun (congrArg Subtype.val hg) k)
      rw [← h'.closure_eq_iv (fun k => (a.1 k).2) a.2] at hx
      have hle : closure (Set.range fun k => ((a.1 k : ↥(cModZ h'.sub)) : G)) ≤
          centralizer {(g : G)} := by
        rw [closure_le]
        rintro _ ⟨k, rfl⟩
        rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
        calc ((a.1 k : ↥(cModZ h'.sub)) : G) * g =
            ((g : G) * a.1 k * (g : G)⁻¹) * g := by rw [hfix k]
          _ = g * a.1 k := by group
      exact mem_centralizer_singleton_iff.mp (hle hx)
    · intro hg
      apply Subtype.ext
      funext k
      apply Subtype.ext
      change (g : G) * a.1 k * (g : G)⁻¹ = a.1 k
      rw [← hg _ (a.1 k).2]
      group
  have hdvd := index_dvd_card_of_forall_stabilizer hstab
  have hSg : Nat.card Sg = 1920 := h'.card_sigma
  rw [hSg] at hdvd
  set C := (centralizer (cModZ h'.sub : Set G)).subgroupOf W₁ with hC
  have hi := C.index_mul_card
  obtain ⟨n, hn'⟩ := IsPGroup.iff_card.mp hW₁
  have hidx : C.index ∣ 2 ^ n := hn' ▸ C.index_dvd_card
  obtain ⟨k, -, hkeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hidx
  have hk7 : k ≤ 7 := by
    by_contra hk8
    have h8 : 2 ^ 8 ∣ 1920 := (Nat.pow_dvd_pow 2 (by omega : 8 ≤ k)).trans (hkeq ▸ hdvd)
    exact absurd h8 (by norm_num)
  have hidx128 : C.index ≤ 128 := by
    rw [hkeq]
    calc 2 ^ k ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) hk7
      _ = 128 := by norm_num
  by_contra hlt
  have : C.index * Nat.card C ≤ 128 * 7 := Nat.mul_le_mul hidx128 (by omega)
  omega

end IdxModel

end EndB

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

namespace EndB.JLayer

variable {hs : Setting46e t L p f S w z V i j}
  {π : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) →* P}

theorem exists_lambda
    (hKC : AutPSL2CentralizerInput) (hJ : JLayer hs π)
    (hπi : Function.Injective π)
    (hQ : pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) =
      zpowers (betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) {W : Subgroup X}
    (hW : IsSylowOf 2 W (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)))
    (hUW : V ⊓ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) ≤ W) {y : X}
    (hyN : y ∈ normalizer (W : Set X)) (hyW : y ∉ W) (hy2 : y ^ 2 ∈ W)
    (hy2grp : IsPGroup 2 ↥(W ⊔ zpowers y))
    (hyb : y * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * y⁻¹ =
      w ^ (orderOf w / 2) * t ^ i * z ^ j * z) (hyz : y * z * y⁻¹ = z)
    {c : Equiv.Perm (Fin 315)} (hcR : c ∈ R) {e' : ℕ → X} (h' : IdxModel 128 e' vT vI 0)
    (hsub : h'.sub = W ⊓ oP W)
    (hφ : ∀ k < 128, ∃ hk : e' k ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X),
      ∃ hkE : (QuotientGroup.mk ⟨e' k, hk⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∈
        layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)),
      c⁻¹ * ((π ⟨_, hkE⟩ : P) : Equiv.Perm (Fin 315)) * c = vE k) :
    z ∈ zW W ∧ z = e' 1 ∧ ∃ l ∈ W ⊔ zpowers y, l ∉ W ∧ l * l = 1 ∧
      (∀ a ∈ cModZ (W ⊓ oP W), l * a = a * l) ∧
      l * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * l⁻¹ = w ^ (orderOf w / 2) * t ^ i * z ^ j * z ∧
      l * z * l⁻¹ = z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  have hWM := hW.le
  obtain ⟨hβZ, -⟩ := Standing.Setup42.center_W hKC hs.setup hs.sylow_V hs.le_V hs.beta hW hUW
  have hβW : β ∈ W := (mem_inf.mp hβZ).1
  have hβ2 : β ^ 2 = 1 := hs.setup.sq_eq_one_of_mem_X (beta_mem_X i j)
  have hz2 : z ^ 2 = 1 := by rw [← hs.setup.z_order]; exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by
    intro h
    have := hs.setup.z_order
    rw [h, orderOf_one] at this
    exact absurd this (by norm_num)
  have hzZ : z ∈ zW W := by
    have h1 := conj_mem_zW y hyN β hβZ
    rw [hyb] at h1
    have h2 := mul_mem (inv_mem hβZ) h1
    rwa [inv_mul_cancel_left] at h2
  have hzW : z ∈ W := (mem_inf.mp hzZ).1
  have hcomm_z : ∀ g ∈ W, g * z = z * g := fun g hg =>
    mem_centralizer_iff.mp (mem_inf.mp hzZ).2 g hg
  have hzK : z ∈ centralizerResidual L β := hs.lemma45.z_mem.2
  have hzM : z ∈ centralizer ({β} : Set X) := K_le_centralizer_beta i j hzK
  have hzE : (QuotientGroup.mk ⟨z, hWM hzW⟩ : MBar β) ∈ layer (MBar β) :=
    hs.KBar_le_layer ⟨⟨z, hzM⟩, hzK, rfl⟩
  have hzV : z ∈ W ⊓ oP W := hJ.mem_V0_of_bar_mem hKC hπi hW hUW hzW hzE
  have hze : z = e' 1 := by
    rcases h'.center_eq vIndex_facts.2.1 (by rw [hsub]; exact hzV) (fun x hx =>
      (hcomm_z x (mem_inf.mp (by rw [← hsub]; exact hx : x ∈ W ⊓ oP W)).1).symm) with h | h
    · exact absurd h hz1
    · exact h
  refine ⟨hzZ, hze, ?_⟩
  have hyn : ∀ k ∈ W, y * k * y⁻¹ ∈ W := fun k hk => conj_mem_W y hyN k hk
  have hW₁N : W ⊔ zpowers y ≤ normalizer (W : Set X) :=
    sup_le le_normalizer_self (zpowers_le.mpr hyN)
  have hyz' : y * z = z * y := by
    calc y * z = (y * z * y⁻¹) * y := by group
      _ = z * y := by rw [hyz]
  have hW₁C : W ⊔ zpowers y ≤ centralizer ({z} : Set X) :=
    sup_le (fun g hg => mem_centralizer_singleton_iff.mpr (hcomm_z g hg))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hyz'))
  have hW₁z : ∀ g ∈ W ⊔ zpowers y, g * z * g⁻¹ = z := fun g hg => by
    rw [mem_centralizer_singleton_iff.mp (hW₁C hg), mul_inv_cancel_right]
  have hn : ∀ g ∈ W ⊔ zpowers y, ∀ x ∈ h'.sub, g * x * g⁻¹ ∈ h'.sub := by
    rw [hsub]
    exact fun g hg => conj_mem_inf' conj_mem_W conj_mem_oP g (hW₁N hg)
  have hV₀ : Nat.card ↥(W ⊓ oP W) = 128 := by rw [← hsub, h'.card_sub]
  have hcardW := hJ.card_W_ge hKC hπi hW hUW hV₀
  have hcard₁ := card_sup_zpowers hyn hy2 hyW
  have hcent := h'.card_centralizer_ge hy2grp (by omega) hn (by rw [← hze]; exact hW₁z)
  have hbasis : ∀ k ∈ vBasis, e' k ∈ cModZ h'.sub := fun k hk => by
    refine h'.mem_iv_iff.mpr ⟨k, ?_, rfl⟩
    simp only [vBasis, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> simp [ivList]
  have hle4 : ∀ g : ↥((centralizer (cModZ h'.sub : Set X)).subgroupOf (W ⊔ zpowers y)),
      ((g : ↥(W ⊔ zpowers y)) : X) ∈ W →
        ((g : ↥(W ⊔ zpowers y)) : X) ∈ ({1, β, e' 1, β * e' 1} : Set X) := by
    intro g hgW
    have hgc := mem_centralizer_iff.mp (Subgroup.mem_subgroupOf.mp g.2)
    rcases hJ.eq_of_comm_basis hQ hW hβW hcR h' hsub hφ hgW
      (fun k hk => (hgc _ (hbasis k hk)).symm) with h | h | h | h <;> simp [h, hβ]
  have hex : ∃ g : ↥((centralizer (cModZ h'.sub : Set X)).subgroupOf (W ⊔ zpowers y)),
      ((g : ↥(W ⊔ zpowers y)) : X) ∉ W := by
    by_contra hcon
    push Not at hcon
    have hinj : Function.Injective
        (fun g : ↥((centralizer (cModZ h'.sub : Set X)).subgroupOf (W ⊔ zpowers y)) =>
          (⟨((g : ↥(W ⊔ zpowers y)) : X), hle4 g (hcon g)⟩ :
            ↥({1, β, e' 1, β * e' 1} : Set X))) :=
      fun a b hab => by
        simp only [Subtype.mk.injEq] at hab
        exact Subtype.ext (Subtype.ext hab)
    have h1 := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_coe_set_eq] at h1
    have h2 := Set.ncard_insert_le (1 : X) ({β, e' 1, β * e' 1} : Set X)
    have h3 := Set.ncard_insert_le β ({e' 1, β * e' 1} : Set X)
    have h4 := Set.ncard_insert_le (e' 1) ({β * e' 1} : Set X)
    have h5 := Set.ncard_singleton (β * e' 1)
    omega
  obtain ⟨⟨⟨l₀, hl₀W₁⟩, hl₀C⟩, hl₀W⟩ := hex
  change l₀ ∉ W at hl₀W
  have hl₀c : ∀ a ∈ cModZ h'.sub, a * l₀ = l₀ * a :=
    mem_centralizer_iff.mp (Subgroup.mem_subgroupOf.mp hl₀C)
  have hl₀y : l₀ * y⁻¹ ∈ W := by
    rcases (mem_sup_zpowers_iff hyn hy2).mp hl₀W₁ with h | h
    · exact absurd h hl₀W
    · exact h
  have hl₀b : l₀ * β * l₀⁻¹ = β * z := by
    have h1 : l₀ * β * l₀⁻¹ = (l₀ * y⁻¹) * (y * β * y⁻¹) * (l₀ * y⁻¹)⁻¹ := by group
    rw [h1, hyb]
    have h2 : (l₀ * y⁻¹) * (β * z) = (β * z) * (l₀ * y⁻¹) :=
      mem_centralizer_iff.mp (mem_inf.mp (mul_mem hβZ hzZ)).2 _ hl₀y
    rw [h2, mul_inv_cancel_right]
  have hl₀z := hW₁z l₀ hl₀W₁
  have hl₀2 : l₀ * l₀ ∈ W := by
    rw [show l₀ * l₀ = (l₀ * y⁻¹) * (y * (l₀ * y⁻¹) * y⁻¹) * y ^ 2 by group]
    exact mul_mem (mul_mem hl₀y (hyn _ hl₀y)) hy2
  have hl₀2c : ∀ k ∈ vBasis, (l₀ * l₀) * e' k = e' k * (l₀ * l₀) := fun k hk => by
    have h1 := hl₀c _ (hbasis k hk)
    calc l₀ * l₀ * e' k = l₀ * (l₀ * e' k) := by group
      _ = l₀ * (e' k * l₀) := by rw [← h1]
      _ = (l₀ * e' k) * l₀ := by group
      _ = (e' k * l₀) * l₀ := by rw [← h1]
      _ = e' k * (l₀ * l₀) := by group
  have hβ2' : β * β = 1 := by rw [← sq]; exact hβ2
  have hz2' : z * z = 1 := by rw [← sq]; exact hz2
  have hβz : β * z = z * β := (hcomm_z β hβW)
  have hcV : ∀ a ∈ cModZ (W ⊓ oP W), β * a = a * β := fun a ha =>
    (mem_centralizer_iff.mp (mem_inf.mp hβZ).2 a (mem_inf.mp (cModZ_le _ ha)).1).symm
  rw [← hsub]
  rcases hJ.eq_of_comm_basis hQ hW hβW hcR h' hsub hφ hl₀2 hl₀2c with h | h | h | h
  ·
    exact ⟨l₀, hl₀W₁, hl₀W, h, fun a ha => (hl₀c a ha).symm, hl₀b, hl₀z⟩
  ·
    exfalso
    apply hz1
    have h' : β = l₀ * l₀ := h.symm
    have h1 : l₀ * β * l₀⁻¹ = β := by
      rw [h']
      group
    rw [hl₀b] at h1
    have h2 := congrArg (β⁻¹ * ·) h1
    simp only [inv_mul_cancel_left, inv_mul_cancel] at h2
    exact h2
  ·
    rw [← hze] at h
    refine ⟨l₀ * β, mul_mem hl₀W₁ (mem_sup_left hβW), fun hW' => hl₀W ?_, ?_, fun a ha => ?_, ?_,
      ?_⟩
    · rw [show l₀ = (l₀ * β) * β⁻¹ by group]
      exact mul_mem hW' (inv_mem hβW)
    · calc l₀ * β * (l₀ * β) = (l₀ * β * l₀⁻¹) * (l₀ * l₀) * β := by group
        _ = 1 := by
          rw [hl₀b, h, mul_assoc β z z, hz2', mul_one, hβ2']
    · have h1 := (hl₀c a ha).symm
      have h2 := hcV a (by rw [← hsub]; exact ha)
      calc l₀ * β * a = l₀ * (β * a) := by group
        _ = l₀ * (a * β) := by rw [h2]
        _ = (l₀ * a) * β := by group
        _ = (a * l₀) * β := by rw [h1]
        _ = a * (l₀ * β) := by group
    · calc l₀ * β * β * (l₀ * β)⁻¹ = l₀ * β * l₀⁻¹ := by group
        _ = β * z := hl₀b
    · calc l₀ * β * z * (l₀ * β)⁻¹ = l₀ * (β * z * β⁻¹) * l₀⁻¹ := by group
        _ = l₀ * z * l₀⁻¹ := by rw [hβz]; group
        _ = z := hl₀z
  ·
    exfalso
    apply hz1
    rw [← hze] at h
    have h' : β * z = l₀ * l₀ := h.symm
    have h1 : l₀ * (β * z) * l₀⁻¹ = β * z := by
      rw [h']
      group
    have h2 : l₀ * (β * z) * l₀⁻¹ = (l₀ * β * l₀⁻¹) * (l₀ * z * l₀⁻¹) := by group
    rw [h2, hl₀b, hl₀z, mul_assoc, hz2', mul_one] at h1
    have h3 := congrArg (β⁻¹ * ·) h1
    simp only [inv_mul_cancel_left, inv_mul_cancel] at h3
    exact h3.symm

end EndB.JLayer

end CFSG.ComponentClassification.HarrisLit
