module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec5GDefs
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec5

public section

namespace CFSG.ComponentClassification.AS76b.Sec5

open Subgroup CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type} [Group G]

section Comm

variable {V : Subgroup G}

theorem mul_comm_of_two (two : ∀ v ∈ V, v * v = 1) {a b : G} (ha : a ∈ V) (hb : b ∈ V) :
    a * b = b * a := by
  have hinv : ∀ c ∈ V, c⁻¹ = c := fun c hc => inv_eq_of_mul_eq_one_right (two c hc)
  calc a * b = (a * b)⁻¹ := (hinv _ (V.mul_mem ha hb)).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [hinv b hb, hinv a ha]

theorem exists_mul_of_mem_sup (two : ∀ v ∈ V, v * v = 1) {K L : Subgroup G} (hK : K ≤ V)
    (hL : L ≤ V) {g : G} (hg : g ∈ K ⊔ L) : ∃ k ∈ K, ∃ l ∈ L, k * l = g := by
  let S : Subgroup G :=
    { carrier := {g | ∃ k ∈ K, ∃ l ∈ L, k * l = g}
      mul_mem' := by
        rintro _ _ ⟨k, hk, l, hl, rfl⟩ ⟨k', hk', l', hl', rfl⟩
        refine ⟨k * k', K.mul_mem hk hk', l * l', L.mul_mem hl hl', ?_⟩
        rw [mul_assoc k l, ← mul_assoc l k' l', mul_comm_of_two two (hL hl) (hK hk'),
          mul_assoc k' l l', ← mul_assoc k k' (l * l')]
      one_mem' := ⟨1, K.one_mem, 1, L.one_mem, mul_one 1⟩
      inv_mem' := by
        rintro _ ⟨k, hk, l, hl, rfl⟩
        refine ⟨k⁻¹, K.inv_mem hk, l⁻¹, L.inv_mem hl, ?_⟩
        rw [mul_inv_rev, mul_comm_of_two two (hL (L.inv_mem hl)) (hK (K.inv_mem hk))] }
  have hle : K ⊔ L ≤ S := sup_le (fun k hk => ⟨k, hk, 1, L.one_mem, mul_one k⟩)
    (fun l hl => ⟨1, K.one_mem, l, hl, one_mul l⟩)
  exact hle hg

end Comm

@[expose] def EA (V X : Subgroup G) (_two : ∀ v ∈ V, v * v = 1)
    (_hX : X ≤ normalizer (V : Set G)) : Type :=
  Additive V

namespace EA

variable {V X : Subgroup G} {two : ∀ v ∈ V, v * v = 1} {hX : X ≤ normalizer (V : Set G)}

abbrev commGroup (two : ∀ v ∈ V, v * v = 1) : CommGroup V :=
  { V.toGroup with mul_comm := fun a b => Subtype.ext (mul_comm_of_two two a.2 b.2) }

instance : AddCommGroup (EA V X two hX) := @Additive.addCommGroup V (commGroup two)

instance [Finite G] : Finite (EA V X two hX) := inferInstanceAs (Finite V)

@[expose] def toG (a : EA V X two hX) : G := ((Additive.toMul a : V) : G)

@[expose] def ofV (v : V) : EA V X two hX := Additive.ofMul v

@[simp] theorem toG_ofV (v : V) : toG (ofV (two := two) (hX := hX) v) = v := rfl

theorem toG_mem (a : EA V X two hX) : toG a ∈ V := (Additive.toMul a).2

theorem toG_injective : Function.Injective (toG (two := two) (hX := hX)) :=
  fun _ _ hab => Additive.toMul.injective (Subtype.ext hab)

@[simp] theorem toG_add (a b : EA V X two hX) : toG (a + b) = toG a * toG b := rfl

@[simp] theorem toG_zero : toG (0 : EA V X two hX) = 1 := rfl

theorem eq_zero_iff {a : EA V X two hX} : a = 0 ↔ toG a = 1 :=
  ⟨fun h0 => h0 ▸ rfl, fun h1 => toG_injective h1⟩

theorem exists_toG {g : G} (hg : g ∈ V) : ∃ a : EA V X two hX, toG a = g := ⟨ofV ⟨g, hg⟩, rfl⟩

@[expose] def conj (x : X) (a : EA V X two hX) : EA V X two hX :=
  ofV ⟨(x : G) * toG a * (x : G)⁻¹, (mem_normalizer_iff.1 (hX x.2) _).1 (toG_mem a)⟩

@[simp] theorem toG_conj (x : X) (a : EA V X two hX) :
    toG (conj x a) = (x : G) * toG a * (x : G)⁻¹ := rfl

instance : DistribMulAction X (EA V X two hX) where
  smul := conj
  one_smul a := toG_injective (show toG (conj 1 a) = toG a by simp)
  mul_smul x y a := toG_injective
    (show toG (conj (x * y) a) = toG (conj x (conj y a)) by simp [mul_assoc])
  smul_zero x := toG_injective (show toG (conj x 0) = toG 0 by simp)
  smul_add x a b := toG_injective
    (show toG (conj x (a + b)) = toG (conj x a + conj x b) by simp [mul_assoc])

@[simp] theorem toG_smul (x : X) (a : EA V X two hX) :
    toG (x • a) = (x : G) * toG a * (x : G)⁻¹ := rfl

@[expose] def asub (K : Subgroup G) : AddSubgroup (EA V X two hX) where
  carrier := {a | toG a ∈ K}
  add_mem' ha hb := K.mul_mem ha hb
  zero_mem' := K.one_mem
  neg_mem' ha := K.inv_mem ha

@[simp] theorem mem_asub {K : Subgroup G} {a : EA V X two hX} : a ∈ asub K ↔ toG a ∈ K := Iff.rfl

theorem asub_inf (K L : Subgroup G) :
    asub (K ⊓ L) = (asub K ⊓ asub L : AddSubgroup (EA V X two hX)) := by
  ext a
  simp [AddSubgroup.mem_inf]

theorem asub_bot : asub ⊥ = (⊥ : AddSubgroup (EA V X two hX)) := by
  ext a
  simp [eq_zero_iff]

theorem asub_V : asub V = (⊤ : AddSubgroup (EA V X two hX)) := by
  ext a
  simp [toG_mem]

theorem asub_mono {K L : Subgroup G} (hKL : K ≤ L) :
    asub K ≤ (asub L : AddSubgroup (EA V X two hX)) := fun _ ha => hKL ha

theorem asub_le_asub_iff {K L : Subgroup G} (hK : K ≤ V) :
    (asub K : AddSubgroup (EA V X two hX)) ≤ asub L ↔ K ≤ L := by
  refine ⟨fun hKL g hg => ?_, asub_mono⟩
  obtain ⟨a, rfl⟩ := exists_toG (two := two) (hX := hX) (hK hg)
  exact hKL hg

theorem asub_inj {K L : Subgroup G} (hK : K ≤ V) (hL : L ≤ V)
    (hKL : (asub K : AddSubgroup (EA V X two hX)) = asub L) : K = L :=
  le_antisymm ((asub_le_asub_iff hK).1 hKL.le) ((asub_le_asub_iff hL).1 hKL.ge)

theorem asub_eq_bot_iff {K : Subgroup G} (hK : K ≤ V) :
    (asub K : AddSubgroup (EA V X two hX)) = ⊥ ↔ K = ⊥ :=
  ⟨fun hK0 => asub_inj hK bot_le (hK0.trans asub_bot.symm), fun hK0 => by rw [hK0, asub_bot]⟩

theorem asub_sup {K L : Subgroup G} (hK : K ≤ V) (hL : L ≤ V) :
    asub (K ⊔ L) = (asub K ⊔ asub L : AddSubgroup (EA V X two hX)) := by
  refine le_antisymm (fun a ha => ?_) (sup_le (asub_mono le_sup_left) (asub_mono le_sup_right))
  obtain ⟨k, hk, l, hl, hkl⟩ := exists_mul_of_mem_sup two hK hL (mem_asub.1 ha)
  have hsum : a = ofV ⟨k, hK hk⟩ + ofV ⟨l, hL hl⟩ := toG_injective (by simp [hkl])
  rw [hsum]
  exact AddSubgroup.add_mem_sup (mem_asub.2 hk) (mem_asub.2 hl)

theorem card_asub {K : Subgroup G} (hK : K ≤ V) :
    Nat.card (asub K : AddSubgroup (EA V X two hX)) = Nat.card K :=
  Nat.card_congr ⟨fun a => ⟨toG (a : EA V X two hX), a.2⟩, fun k => ⟨ofV ⟨k, hK k.2⟩, k.2⟩,
    fun _ => Subtype.ext (toG_injective rfl), fun _ => rfl⟩

theorem img_asub (x : X) (K : Subgroup G) :
    img x (asub K) = (asub (rightConjugate K (x : G)⁻¹) : AddSubgroup (EA V X two hX)) := by
  ext a
  rw [mem_img_iff_inv_smul, mem_asub, mem_asub, mem_rightConjugate_iff, toG_smul]
  simp

end EA

open EA

namespace GHyp51

variable {V R U W X A B : Subgroup G} (h : GHyp51 V R U W X A B)
include h

theorem le_V_of_mem {T : Subgroup G} (hT : T ∈ gMembers X R) : T ≤ V := by
  obtain ⟨y, hy, rfl⟩ := hT
  intro g hg
  rw [mem_rightConjugate_iff] at hg
  exact (mem_normalizer_iff.1 (h.X_le hy) g).2 (h.R_le hg)

theorem mem_members_iff {T' : AddSubgroup (EA V X h.two h.X_le)} :
    T' ∈ members X (asub R) ↔ ∃ T ∈ gMembers X R, asub T = T' := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨rightConjugate R (x : G)⁻¹, ⟨(x : G)⁻¹, X.inv_mem x.2, rfl⟩, (img_asub x R).symm⟩
  · rintro ⟨T, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨(⟨y, hy⟩ : X)⁻¹, ?_⟩
    rw [img_asub]
    simp

theorem mem_fused_iff (a : EA V X h.two h.X_le) : a ∈ fused X (asub R) ↔ toG a ∈ gFused X R := by
  constructor
  · rintro ⟨x, r, hr, hr0, rfl⟩
    refine ⟨(x : G)⁻¹, X.inv_mem x.2, toG r, hr, fun h1 => hr0 (eq_zero_iff.2 h1), ?_⟩
    rw [toG_smul, inv_inv]
  · rintro ⟨y, hy, r, hr, hr0, hyr⟩
    obtain ⟨r', rfl⟩ := exists_toG (two := h.two) (hX := h.X_le) (h.R_le hr)
    refine ⟨(⟨y, hy⟩ : X)⁻¹, r', hr, fun h1 => hr0 (by rw [h1]; rfl), toG_injective ?_⟩
    rw [toG_smul, ← hyr]
    simp

theorem hyp51 : Hyp51 X (A.subgroupOf X) (B.subgroupOf X)
    (asub R : AddSubgroup (EA V X h.two h.X_le)) (asub U) (asub W) where
  two a := toG_injective (h.two _ (toG_mem a))
  decomp :=
    ⟨by rw [← asub_sup h.R_le h.U_le, ← asub_sup (sup_le h.R_le h.U_le) h.W_le, h.sup_eq, asub_V],
      by rw [← asub_sup h.U_le h.W_le, ← asub_inf, h.inf_R, asub_bot],
      by rw [← asub_inf, h.inf_U, asub_bot]⟩
  two_lt := by rw [card_asub h.R_le]; exact h.two_lt
  card_eq := by rw [card_asub h.U_le, card_asub h.W_le]; exact h.card_eq
  A_fix := by
    intro a ha v hv
    rw [← asub_sup h.R_le h.U_le, mem_asub] at hv
    have hc : A ≤ centralizer ((R ⊔ U : Subgroup G) : Set G) :=
      le_centralizer_iff.2 (sup_le (le_centralizer_iff.1 h.A_centR)
        (le_centralizer_iff.1 h.A_centU))
    apply toG_injective
    rw [toG_smul, ← mem_centralizer_iff.1 (hc (mem_subgroupOf.1 ha)) _ hv, mul_inv_cancel_right]
  B_fix := by
    intro b hb v hv
    rw [← asub_sup h.R_le h.W_le, mem_asub] at hv
    have hc : B ≤ centralizer ((R ⊔ W : Subgroup G) : Set G) :=
      le_centralizer_iff.2 (sup_le (le_centralizer_iff.1 h.B_centR)
        (le_centralizer_iff.1 h.B_centW))
    apply toG_injective
    rw [toG_smul, ← mem_centralizer_iff.1 (hc (mem_subgroupOf.1 hb)) _ hv, mul_inv_cancel_right]
  A_W a ha w hw :=
    mem_asub.2 ((mem_normalizer_iff.1 (h.A_normW (mem_subgroupOf.1 ha)) _).1 (mem_asub.1 hw))
  B_U b hb u hu :=
    mem_asub.2 ((mem_normalizer_iff.1 (h.B_normU (mem_subgroupOf.1 hb)) _).1 (mem_asub.1 hu))
  A_trans := by
    intro w hw w' hw' hw0 hw'0
    obtain ⟨a, ha, haw⟩ := h.A_trans _ hw _ hw' (fun h1 => hw0 (eq_zero_iff.2 h1))
      (fun h1 => hw'0 (eq_zero_iff.2 h1))
    refine ⟨⟨a⁻¹, h.A_le (A.inv_mem ha)⟩, mem_subgroupOf.2 (A.inv_mem ha), toG_injective ?_⟩
    rw [toG_smul]
    simpa using haw
  B_trans := by
    intro u hu u' hu' hu0 hu'0
    obtain ⟨b, hb, hbu⟩ := h.B_trans _ hu _ hu' (fun h1 => hu0 (eq_zero_iff.2 h1))
      (fun h1 => hu'0 (eq_zero_iff.2 h1))
    refine ⟨⟨b⁻¹, h.B_le (B.inv_mem hb)⟩, mem_subgroupOf.2 (B.inv_mem hb), toG_injective ?_⟩
    rw [toG_smul]
    simpa using hbu
  A_free := by
    intro a ha w hw hw0 haw w' hw'
    have hfix : (a : G)⁻¹⁻¹ * toG w * (a : G)⁻¹ = toG w := by
      rw [inv_inv]
      exact congrArg toG haw
    have hc := h.A_fix _ (A.inv_mem (mem_subgroupOf.1 ha)) _ hw
      (fun h1 => hw0 (eq_zero_iff.2 h1)) hfix
    have hc' : (a : G) ∈ centralizer (W : Set G) := by
      simpa using (centralizer (W : Set G)).inv_mem hc
    apply toG_injective
    rw [toG_smul, ← mem_centralizer_iff.1 hc' _ hw', mul_inv_cancel_right]
  B_free := by
    intro b hb u hu hu0 hbu u' hu'
    have hfix : (b : G)⁻¹⁻¹ * toG u * (b : G)⁻¹ = toG u := by
      rw [inv_inv]
      exact congrArg toG hbu
    have hc := h.B_fix _ (B.inv_mem (mem_subgroupOf.1 hb)) _ hu
      (fun h1 => hu0 (eq_zero_iff.2 h1)) hfix
    have hc' : (b : G) ∈ centralizer (U : Set G) := by
      simpa using (centralizer (U : Set G)).inv_mem hc
    apply toG_injective
    rw [toG_smul, ← mem_centralizer_iff.1 hc' _ hu', mul_inv_cancel_right]
  normal := by
    intro n hn a ha b hb
    have hnR : (n : G) ∈ normalizer (R : Set G) := by
      rw [mem_normalizer_iff]
      intro g
      constructor
      · intro hg
        obtain ⟨r, rfl⟩ := exists_toG (two := h.two) (hX := h.X_le) (h.R_le hg)
        have hr : n • r ∈ asub R := hn ▸ smul_mem_img (mem_asub.2 hg)
        simpa using hr
      · intro hg
        obtain ⟨c, hc⟩ := exists_toG (two := h.two) (hX := h.X_le) (h.R_le hg)
        have hcR : c ∈ img n (asub R) := by
          rw [hn]
          exact mem_asub.2 (hc ▸ hg)
        obtain ⟨r, hr, hrc⟩ := mem_img.1 hcR
        have he : (n : G) * toG r * (n : G)⁻¹ = (n : G) * g * (n : G)⁻¹ := by
          rw [← hc, ← hrc]
          rfl
        have hrg : toG r = g := by simpa using he
        rw [← hrg]
        exact hr
    obtain ⟨a', ha', b', hb', c, hc, habc⟩ :=
      h.normal n n.2 hnR a (mem_subgroupOf.1 ha) b (mem_subgroupOf.1 hb)
    refine ⟨⟨a', h.A_le ha'⟩, mem_subgroupOf.2 ha', ⟨b', h.B_le hb'⟩, mem_subgroupOf.2 hb',
      fun v => toG_injective ?_⟩
    have hcv : c * toG v = toG v * c := (mem_centralizer_iff.1 hc _ (toG_mem v)).symm
    rw [toG_smul, toG_smul]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [habc]
    calc a' * b' * c * toG v * (a' * b' * c)⁻¹ = a' * b' * (c * toG v) * c⁻¹ * (a' * b')⁻¹ := by
          group
      _ = a' * b' * (toG v * c) * c⁻¹ * (a' * b')⁻¹ := by rw [hcv]
      _ = a' * b' * toG v * (a' * b')⁻¹ := by group
  one := by
    intro T' hT' hT'R
    obtain ⟨T, hT, rfl⟩ := (mem_members_iff h).1 hT'
    have hTR : T ≠ R := fun e => hT'R (by rw [e])
    obtain ⟨h1, h2⟩ := h.one T hT hTR
    refine ⟨by rw [← asub_inf, h1, asub_bot], ?_⟩
    rcases h2 with h2 | h2 | ⟨h2, h3⟩
    · exact Or.inl (by rw [← asub_sup h.R_le h.U_le]; exact asub_mono h2)
    · exact Or.inr (Or.inl (by rw [← asub_sup h.R_le h.W_le]; exact asub_mono h2))
    · exact Or.inr (Or.inr ⟨by rw [← asub_sup h.R_le h.U_le, ← asub_inf, h2, asub_bot],
        by rw [← asub_sup h.R_le h.W_le, ← asub_inf, h3, asub_bot]⟩)
  twoU := by
    intro T' hT' hle
    obtain ⟨T, hT, rfl⟩ := (mem_members_iff h).1 hT'
    rw [← asub_sup h.R_le h.U_le, asub_le_asub_iff (h.le_V_of_mem hT)] at hle
    rcases h.twoU T hT hle with ⟨rfl, hall⟩ | h2
    · refine Or.inl ⟨rfl, fun S' hS' hSle => ?_⟩
      obtain ⟨S, hS, rfl⟩ := (mem_members_iff h).1 hS'
      rw [← asub_sup h.R_le h.U_le, asub_le_asub_iff (h.le_V_of_mem hS)] at hSle
      rcases hall S hS hSle with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · exact Or.inr (by rw [← asub_inf, h2, asub_bot])
  twoW := by
    intro T' hT' hle
    obtain ⟨T, hT, rfl⟩ := (mem_members_iff h).1 hT'
    rw [← asub_sup h.R_le h.W_le, asub_le_asub_iff (h.le_V_of_mem hT)] at hle
    rcases h.twoW T hT hle with ⟨rfl, hall⟩ | h2
    · refine Or.inl ⟨rfl, fun S' hS' hSle => ?_⟩
      obtain ⟨S, hS, rfl⟩ := (mem_members_iff h).1 hS'
      rw [← asub_sup h.R_le h.W_le, asub_le_asub_iff (h.le_V_of_mem hS)] at hSle
      rcases hall S hS hSle with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · exact Or.inr (by rw [← asub_inf, h2, asub_bot])
  three := by
    obtain ⟨T, hT, h1, h2, h3⟩ := h.three
    refine ⟨asub T, (mem_members_iff h).2 ⟨T, hT, rfl⟩,
      fun e => h1 (asub_inj (h.le_V_of_mem hT) h.R_le e), ?_, ?_⟩
    · rw [← asub_sup h.R_le h.U_le, ← asub_inf, h2, asub_bot]
    · rw [← asub_sup h.R_le h.W_le, ← asub_inf, h3, asub_bot]

theorem gFused_eq (hf : fused X (asub R : AddSubgroup (EA V X h.two h.X_le)) =
      ((asub U ⊔ asub W : AddSubgroup (EA V X h.two h.X_le)) : Set (EA V X h.two h.X_le))ᶜ) :
    gFused X R = (V : Set G) \ ((U ⊔ W : Subgroup G) : Set G) := by
  ext g
  simp only [Set.mem_sdiff, SetLike.mem_coe]
  constructor
  · intro hg
    have hgV : g ∈ V := by
      obtain ⟨y, hy, r, hr, -, rfl⟩ := hg
      exact (mem_normalizer_iff''.1 (h.X_le hy) r).1 (h.R_le hr)
    obtain ⟨a, rfl⟩ := exists_toG (two := h.two) (hX := h.X_le) hgV
    have ha : a ∈ fused X (asub R) := (h.mem_fused_iff a).2 hg
    rw [hf, Set.mem_compl_iff, SetLike.mem_coe, ← asub_sup h.U_le h.W_le, mem_asub] at ha
    exact ⟨hgV, ha⟩
  · rintro ⟨hgV, hgUW⟩
    obtain ⟨a, rfl⟩ := exists_toG (two := h.two) (hX := h.X_le) hgV
    have ha : a ∈ fused X (asub R) := by
      rw [hf, Set.mem_compl_iff, SetLike.mem_coe, ← asub_sup h.U_le h.W_le, mem_asub]
      exact hgUW
    exact (h.mem_fused_iff a).1 ha

theorem ncard_members :
    (members X (asub R : AddSubgroup (EA V X h.two h.X_le))).ncard = (gMembers X R).ncard := by
  have he : members X (asub R : AddSubgroup (EA V X h.two h.X_le)) = asub '' gMembers X R := by
    ext T'
    rw [mem_members_iff h, Set.mem_image]
  rw [he]
  exact Set.InjOn.ncard_image fun T hT T₂ hT₂ e =>
    asub_inj (h.le_V_of_mem hT) (h.le_V_of_mem hT₂) e

theorem exists_of_exists {K L : Subgroup G} (hK : K ≤ V)
    (hT : ∃ T' ∈ members X (asub R : AddSubgroup (EA V X h.two h.X_le)),
      T' ≤ asub R ⊔ asub K ∧ T' ⊓ asub L = ⊥ ∧ T' ⊓ asub R = ⊥) :
    ∃ T ∈ gMembers X R, T ≤ R ⊔ K ∧ T ⊓ L = ⊥ ∧ T ⊓ R = ⊥ := by
  obtain ⟨T', hT', hle, hTL, hTR⟩ := hT
  obtain ⟨T, hT, rfl⟩ := (mem_members_iff h).1 hT'
  have hTV := h.le_V_of_mem hT
  rw [← asub_sup h.R_le hK, asub_le_asub_iff hTV] at hle
  rw [← asub_inf, asub_eq_bot_iff (inf_le_left.trans hTV)] at hTL
  rw [← asub_inf, asub_eq_bot_iff (inf_le_left.trans hTV)] at hTR
  exact ⟨T, hT, hle, hTL, hTR⟩

theorem mem_of_mem {K : Subgroup G} (hK : K ≤ V)
    (hm : (asub K : AddSubgroup (EA V X h.two h.X_le)) ∈ members X (asub R)) : K ∈ gMembers X R := by
  obtain ⟨T, hT, e⟩ := (mem_members_iff h).1 hm
  rwa [← asub_inj (h.le_V_of_mem hT) hK e]

end GHyp51

variable {V R U W X A B : Subgroup G} [Finite G]

theorem fusionLemmaG_full (h : GHyp51 V R U W X A B) :
    (gFused X R = (V : Set G) \ ((U ⊔ W : Subgroup G) : Set G) ∧
      (gMembers X R).ncard = Nat.card U ^ 2 ∧
      (∃ T ∈ gMembers X R, T ≤ R ⊔ U ∧ T ⊓ U = ⊥ ∧ T ⊓ R = ⊥) ∧
      (∃ T ∈ gMembers X R, T ≤ R ⊔ W ∧ T ⊓ W = ⊥ ∧ T ⊓ R = ⊥)) ∨
    (Nat.card U = 4 ∧ Nat.card R = 4 ∧ U ∈ gMembers X R ∧ W ∈ gMembers X R) := by
  rcases fusionLemma_full h.hyp51 with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · rw [card_asub h.U_le] at h2
    refine Or.inl ⟨h.gFused_eq h1, by rw [← h.ncard_members, h2], ?_, ?_⟩
    · exact h.exists_of_exists h.U_le h3
    · exact h.exists_of_exists h.W_le h4
  · rw [card_asub h.U_le] at h1
    rw [card_asub h.R_le] at h2
    exact Or.inr ⟨h1, h2, h.mem_of_mem h.U_le h3, h.mem_of_mem h.W_le h4⟩

theorem fusionLemmaG_rot (h : GHyp51 V R U W X A B) :
    (gFused X R = (V : Set G) \ ((U ⊔ W : Subgroup G) : Set G) ∧
      (∃ T ∈ gMembers X R, T ≤ R ⊔ U ∧ T ⊓ U = ⊥ ∧ T ⊓ R = ⊥) ∧
      (∃ T ∈ gMembers X R, T ≤ R ⊔ W ∧ T ⊓ W = ⊥ ∧ T ⊓ R = ⊥)) ∨
    (Nat.card U = 4 ∧ Nat.card R = 4 ∧ U ∈ gMembers X R ∧ W ∈ gMembers X R) := by
  rcases fusionLemmaG_full h with ⟨h1, -, h3, h4⟩ | h'
  · exact Or.inl ⟨h1, h3, h4⟩
  · exact Or.inr h'

end CFSG.ComponentClassification.AS76b.Sec5
