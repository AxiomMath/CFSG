module

public import CFSG.Fischer.Classification.PartII.O2G.ThreeProd
public import CFSG.Fischer.Classification.PartII.O2G.ThreePow
public import CFSG.Fischer.Classification.Uniqueness.Principle
public import CFSG.Fischer.Classification.Unitary.Mu
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer LocalU O2Twin
open Classical

namespace O2G

variable {G : Type} [Group G] {D : Set G}

theorem isTwin_conj_of_mem (hP : Pair G D) {x g u v : G} (hg : g ∈ LocalClass D x)
    (h : IsTwin (LocalClass D x) u v) : IsTwin (LocalClass D x) (g * u * g) (g * v * g) := by
  have h' := LocalU.isTwin_conj hP g h
  rwa [Pair.inv_eq hP hg.1, hg.2.2, mul_assoc, Pair.mul_self hP hg.1, mul_one] at h'

theorem isTwin_mul_mul_of_isTwin (hP : Pair G D) {x a y c : G} (h : IsTwin (LocalClass D x) a y)
    (hc : c ∈ LocalClass D x) (hac : a * c ≠ c * a) :
    IsTwin (LocalClass D x) (a * c * a) (y * c * y) := by
  have hyc : y * c ≠ c * y := fun e => hac ((h.2.2.2 c hc).2 e.symm).symm
  have h' := isTwin_conj_of_mem hP hc h
  rwa [Pair.mul_mul_eq hP hc.1 h.1.1 fun e => hac e.symm,
    Pair.mul_mul_eq hP hc.1 h.2.1.1 fun e => hyc e.symm] at h'

theorem image_conj_mul_eq (hP : Pair G D) (hZ : Subgroup.center G = ⊥)
    (hS : IsSimpleGroup (commutator G)) {x t b : G} (hx : x ∈ D) (ht : t ∈ LocalClass D x)
    (hb : b ∈ LocalClass D x) (htb : t * b ≠ b * t) :
    (fun t' => t * t' * b * (t * t')) '' twinClass (LocalClass D x) t =
      twinClass (LocalClass D x) b := by
  have := Pair.finite hP
  have hmaps : Set.MapsTo (fun t' => t * t' * b * (t * t')) (twinClass (LocalClass D x) t)
      (twinClass (LocalClass D x) b) := fun t' ht' =>
    isTwin_conj_mul hP (isTwin_of_mem (self_mem_twinClass ht) ht') hb htb
  have hinj : Set.InjOn (fun t' => t * t' * b * (t * t')) (twinClass (LocalClass D x) t) := by
    intro u hu u' hu' heq
    simp only at heq
    rw [mul_mul_mul_mul_eq hu.2.2.1, mul_mul_mul_mul_eq hu'.2.2.1] at heq
    have h12 : u * b * u = u' * b * u' := by
      rw [← Pair.mul_mul_mul_mul hP ht.1 (u * b * u), heq, Pair.mul_mul_mul_mul hP ht.1]
    have hub : u * b ≠ b * u := fun e => htb ((hu.2.2.2 b hb).2 e.symm).symm
    have hu'b : u' * b ≠ b * u' := fun e => htb ((hu'.2.2.2 b hb).2 e.symm).symm
    have h2 : b * u * b = b * u' * b := by
      rw [← Pair.mul_mul_eq hP hu.2.1.1 hb.1 hub, h12, Pair.mul_mul_eq hP hu'.2.1.1 hb.1 hu'b]
    exact mul_left_cancel (mul_right_cancel h2)
  refine Set.eq_of_subset_of_ncard_le (Set.image_subset_iff.2 hmaps) ?_ (Set.toFinite _)
  rw [hinj.ncard_image, ncard_twinClass_eq hP hZ hS hx hb ht]

theorem four_mul_lt_two_pow {n : ℕ} (hn : 5 ≤ n) : 4 * n < 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ m hm ih => rw [pow_succ]; omega

section Bound

variable (hP : Pair G D) (hZ : Subgroup.center G = ⊥) (hS : IsSimpleGroup (commutator G))
  {x y c : G} (hx : x ∈ D) (hy : y ∈ LocalClass D x) (hc : c ∈ LocalClass D x)
  (hyc : y * c ≠ c * y)
include hP hZ hS hx hy hc hyc

local notation "tp" => sprod (twinClass (LocalClass D x) y) (pairwise_commute_twinClass _ y)

omit hZ hS hx hy in
theorem conj_sprod_mem {X : Finset G} (hX : (X : Set G) ⊆ twinClass (LocalClass D x) y) :
    tp X * c * (tp X)⁻¹
      ∈ twinClass (LocalClass D x) c ∪ twinClass (LocalClass D x) (y * c * y) := by
  induction X using Finset.induction_on with
  | empty =>
    simp only [sprod_empty, one_mul, inv_one, mul_one]; exact Or.inl (self_mem_twinClass hc)
  | insert a X haX ih =>
    have haT : a ∈ twinClass (LocalClass D x) y := hX (Finset.mem_insert_self a X)
    have hXT : (X : Set G) ⊆ twinClass (LocalClass D x) y :=
      fun z hz => hX (Finset.mem_insert_of_mem hz)
    have ha : a ∈ LocalClass D x := haT.2.1
    have hac : a * c ≠ c * a := fun e => hyc ((haT.2.2.2 c hc).2 e.symm).symm
    have hya : IsTwin (LocalClass D x) a y := isTwin_symm haT
    rw [sprod_insert _ haT haX, mul_inv_rev, Pair.inv_eq hP ha.1,
      show a * tp X * c *
          ((tp X)⁻¹ * a) =
        a * (tp X * c *
          (tp X)⁻¹) * a by group]
    have hac' : IsTwin (LocalClass D x) (a * c * a) (y * c * y) :=
      isTwin_mul_mul_of_isTwin hP hya hc hac
    rcases ih hXT with h | h
    ·
      exact Or.inr (isTwin_trans (isTwin_symm hac') (isTwin_conj_of_mem hP ha h))
    ·
      have h1 := isTwin_conj_of_mem hP ha (isTwin_trans hac' h)
      rw [Pair.mul_mul_mul_mul hP ha.1] at h1
      exact Or.inl h1

omit hZ hS hx hy hc hyc in
theorem sprod_injOn
    (hR1 : ∀ X : Finset G, (X : Set G) ⊆ twinClass (LocalClass D x) y →
      tp X = 1 → X = ∅)
    {X Y : Finset G} (hX : (X : Set G) ⊆ twinClass (LocalClass D x) y)
    (hY : (Y : Set G) ⊆ twinClass (LocalClass D x) y)
    (h : tp X = tp Y) :
    X = Y := by
  have hinv : ∀ a ∈ twinClass (LocalClass D x) y, a * a = 1 :=
    fun a ha => Pair.mul_self hP ha.2.1.1
  have h1 : tp (symmDiff X Y) = 1 := by
    rw [← sprod_mul_sprod _ hinv hX hY, h, sprod_mul_self _ hinv]
  have h2 := hR1 _ (fun z hz => by
    rcases Finset.mem_symmDiff.1 hz with h | h
    · exact hX h.1
    · exact hY h.1) h1
  exact symmDiff_eq_bot.1 h2

theorem eq_of_commute_sprod
    (hR1 : ∀ X : Finset G, (X : Set G) ⊆ twinClass (LocalClass D x) y →
      tp X = 1 → X = ∅)
    {X : Finset G} (hX : (X : Set G) ⊆ twinClass (LocalClass D x) y)
    (hu : tp X * c =
      c * tp X) :
    X = ∅ ∨ twinClass (LocalClass D x) y ⊆ X := by
  have := Pair.finite hP
  have hT := pairwise_commute_twinClass (LocalClass D x) y
  have hT2 : ∀ c' ∈ twinClass (LocalClass D x) c,
      tp X * c' = c' * tp X := by
    intro c' hc'
    rw [← image_conj_mul_eq hP hZ hS hx hy hc hyc] at hc'
    obtain ⟨y', hy', rfl⟩ := hc'
    have hcy : Commute y (tp X) :=
      commute_sprod hT (fun a ha => (isTwin_of_mem (self_mem_twinClass hy) ha).2.2.1) X
    have hcy' : Commute y' (tp X) :=
      commute_sprod hT (fun a ha => (isTwin_of_mem hy' ha).2.2.1) X
    have hcc : Commute c (tp X) := hu.symm
    exact ((((hcy.mul_left hcy').mul_left hcc).mul_left (hcy.mul_left hcy')).eq).symm
  have hfix : ∀ c' ∈ twinClass (LocalClass D x) c,
      X.image (fun a => c * c' * a * (c * c')⁻¹) = X := by
    intro c' hc'
    have hcc' : IsTwin (LocalClass D x) c c' := hc'
    have hmaps : ∀ a ∈ twinClass (LocalClass D x) y,
        c * c' * a * (c * c')⁻¹ ∈ twinClass (LocalClass D x) y := by
      intro a ha
      have hca : c * a ≠ a * c := fun e => hyc ((ha.2.2.2 c hc).2 e).symm
      have hinv : (c * c')⁻¹ = c * c' :=
        inv_eq_of_mul_eq_one_right (mul_mul_mul_self hP hc.1 hc'.2.1.1 hcc'.2.2.1)
      rw [hinv]
      exact isTwin_trans ha (isTwin_conj_mul hP hcc' ha.2.1 hca)
    have hcomm : Commute (c * c') (tp X) :=
      (Commute.mul_left (hu.symm) (hT2 c' hc').symm)
    have h1 := conj_sprod hT hT (c * c') hmaps hX
    rw [hcomm.eq, mul_inv_cancel_right] at h1
    refine sprod_injOn hP hR1 ?_ hX h1.symm
    intro z hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hz
    exact hmaps a (hX ha)
  by_cases hne : X = ∅
  · exact Or.inl hne
  right
  obtain ⟨t, ht⟩ := Finset.nonempty_iff_ne_empty.2 hne
  have htT : t ∈ twinClass (LocalClass D x) y := hX ht
  intro t' ht'
  have hct : c * t ≠ t * c := fun e => hyc ((htT.2.2.2 c hc).2 e).symm
  have himg := image_conj_mul_eq hP hZ hS hx hc htT.2.1 hct
  rw [twinClass_eq htT, ← himg] at ht'
  obtain ⟨c', hc', rfl⟩ := ht'
  have hinv : (c * c')⁻¹ = c * c' :=
    inv_eq_of_mul_eq_one_right (mul_mul_mul_self hP hc.1 hc'.2.1.1 hc'.2.2.1)
  rw [← hfix c' hc', Finset.coe_image]
  exact ⟨t, ht, by simp only [hinv]⟩

theorem ncard_twinClass_le_four
    (hR1 : ∀ X : Finset G, (X : Set G) ⊆ twinClass (LocalClass D x) y →
      tp X = 1 → X = ∅) :
    (twinClass (LocalClass D x) y).ncard ≤ 4 := by
  have := Pair.finite hP
  have hT := pairwise_commute_twinClass (LocalClass D x) y
  have hinv : ∀ a ∈ twinClass (LocalClass D x) y, a * a = 1 :=
    fun a ha => Pair.mul_self hP ha.2.1.1
  set r := (twinClass (LocalClass D x) y).ncard with hr
  set Tf := (Set.toFinite (twinClass (LocalClass D x) y)).toFinset with hTf
  set Bf := (Set.toFinite (Subgroup.closure (twinClass (LocalClass D x) y) : Set G)).toFinset
    with hBf
  have hTcard : Tf.card = r := by rw [hr, Set.ncard_eq_toFinset_card _ (Set.toFinite _)]
  have hlow : 2 ^ r ≤ Bf.card := by
    rw [← hTcard, ← Finset.card_powerset]
    refine Finset.card_le_card_of_injOn (fun X => tp X) (fun X _ => ?_) ?_
    · simp only [hBf, Set.Finite.mem_toFinset, SetLike.mem_coe]
      exact sprod_mem_closure hT X
    · intro X hX Y hY h
      simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff,
        Finset.coe_subset] at hX hY
      have hX' : (X : Set G) ⊆ twinClass (LocalClass D x) y := fun z hz => by
        have := hX hz
        rwa [hTf, Set.Finite.mem_toFinset] at this
      have hY' : (Y : Set G) ⊆ twinClass (LocalClass D x) y := fun z hz => by
        have := hY hz
        rwa [hTf, Set.Finite.mem_toFinset] at this
      exact sprod_injOn hP hR1 hX' hY' h
  have hup : Bf.card ≤ 2 * (2 * r) := by
    have h1 := Finset.card_le_mul_card_image (f := fun b => b * c * b⁻¹) Bf 2 ?_
    · refine h1.trans (Nat.mul_le_mul_left 2 ?_)
      have hsub : Bf.image (fun b => b * c * b⁻¹) ⊆
          (Set.toFinite (twinClass (LocalClass D x) c ∪
            twinClass (LocalClass D x) (y * c * y))).toFinset := by
        intro z hz
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hz
        rw [hBf, Set.Finite.mem_toFinset] at hb
        obtain ⟨X, hX, rfl⟩ := exists_eq_sprod hT hinv hb
        rw [Set.Finite.mem_toFinset]
        exact conj_sprod_mem hP hc hyc hX
      refine (Finset.card_le_card hsub).trans ?_
      rw [← Set.ncard_eq_toFinset_card _ (Set.toFinite _)]
      refine (Set.ncard_union_le _ _).trans ?_
      have hycy : y * c * y ∈ LocalClass D x := Pair.mul_mul_mem_localClass_of_mem hP hy hc
      rw [ncard_twinClass_eq hP hZ hS hx hc hy, ncard_twinClass_eq hP hZ hS hx hycy hy]
      omega
    ·
      intro z hz
      obtain ⟨b₀, hb₀, rfl⟩ := Finset.mem_image.1 hz
      refine (Finset.card_le_card (t := {b₀, b₀ * tp Tf}) ?_).trans
        (Finset.card_le_two)
      intro b hb
      rw [Finset.mem_filter] at hb
      obtain ⟨hbB, hbc⟩ := hb
      rw [hBf, Set.Finite.mem_toFinset] at hbB hb₀
      have hu : b₀⁻¹ * b ∈ Subgroup.closure (twinClass (LocalClass D x) y) :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ hb₀) hbB
      obtain ⟨X, hX, hXu⟩ := exists_eq_sprod hT hinv hu
      have hcomm : tp X * c = c * tp X := by
        rw [hXu]
        have : b * c * b⁻¹ = b₀ * c * b₀⁻¹ := hbc
        calc b₀⁻¹ * b * c = b₀⁻¹ * (b * c * b⁻¹) * b := by group
          _ = b₀⁻¹ * (b₀ * c * b₀⁻¹) * b := by rw [this]
          _ = c * (b₀⁻¹ * b) := by group
      rcases eq_of_commute_sprod hP hZ hS hx hy hc hyc hR1 hX hcomm with h | h
      · rw [h, sprod_empty] at hXu
        have : b = b₀ := by
          have := congrArg (b₀ * ·) hXu
          simpa using this.symm
        simp [this]
      · have hXT : X = Tf := by
          ext z
          rw [hTf, Set.Finite.mem_toFinset]
          exact ⟨fun hz => hX hz, fun hz => h hz⟩
        rw [hXT] at hXu
        have : b = b₀ * tp Tf := by rw [hXu, mul_inv_cancel_left]
        simp [this]
  by_contra hgt
  simp only [not_le] at hgt
  have := four_mul_lt_two_pow (n := r) (by omega)
  omega

end Bound

end O2G

end CFSG.Fischer.Classification
