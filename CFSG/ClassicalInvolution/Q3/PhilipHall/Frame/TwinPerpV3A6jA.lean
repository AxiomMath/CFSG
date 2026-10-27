module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6Wt
public import CFSG.Quasithin.H13.J4Order
public import CFSG.Quasithin.H13.J4OrderBase

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.A6jA

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

section Generic

variable {Y : Type} [Group Y]

theorem map_conjSub_hom {A : Type} [Group A] (f : A →* Y) (a : A) (B : Subgroup A) :
    (conjSub a B).map f = conjSub (f a) (B.map f) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : a⁻¹ * y * a ∈ B := mem_conjSub_iff.mp hy
    rw [mem_conjSub_iff]
    refine ⟨a⁻¹ * y * a, hy', ?_⟩
    simp [map_mul, map_inv]
  · intro hx
    rw [mem_conjSub_iff] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    refine ⟨a * y * a⁻¹, conj_mem_conjSub hy, ?_⟩
    rw [map_mul, map_mul, map_inv, hyx]
    group

theorem mem_normalizer_of_conjSub_le [Finite Y] {J : Subgroup Y} {c : Y} (h : conjSub c J ≤ J) :
    c ∈ Subgroup.normalizer (J : Set Y) :=
  mem_normalizer_iff_conjSub_eq.mpr
    (Subgroup.eq_of_le_of_card_ge h (by rw [natCard_conjSub]))

theorem mem_centralizer_of_pow {J : Subgroup Y} {c : Y} {m : ℕ} (hm : Nat.Coprime 3 m)
    (h3 : c ^ 3 ∈ Subgroup.centralizer (J : Set Y))
    (hcm : c ^ m ∈ Subgroup.centralizer (J : Set Y)) :
    c ∈ Subgroup.centralizer (J : Set Y) := by
  have hg := Nat.gcd_eq_gcd_ab 3 m
  rw [hm.gcd_eq_one, Nat.cast_one] at hg
  have : c = (c ^ 3) ^ (Nat.gcdA 3 m) * (c ^ m) ^ (Nat.gcdB 3 m) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, ← hg, zpow_one]
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ h3 _) (Subgroup.zpow_mem _ hcm _)

end Generic

section Model

@[expose] def AE6ModelC1' : Prop :=
  ⨆ (h : AE6Om) (_ : h⁻¹ * ae6ModelZ * h ∈ ae6ModelP), conjSub h⁻¹ ae6ModelP = ⊤

theorem conjSub_mem_twins {c : AE6Om} (hc : c ∈ Subgroup.centralizer ({ae6ModelZ} : Set AE6Om))
    {J : Subgroup AE6Om} (hJ : J ∈ ae6ModelTwins) : conjSub c J ∈ ae6ModelTwins := by
  obtain ⟨g, hg, rfl⟩ := hJ
  exact ⟨c * g, Subgroup.mul_mem _ hc hg, conjSub_mul c g ae6ModelK⟩

theorem conjSub_ae6ModelP {c : AE6Om} (hc : c ∈ Subgroup.centralizer ({ae6ModelZ} : Set AE6Om)) :
    conjSub c ae6ModelP = ae6ModelP := by
  have key : ∀ g ∈ Subgroup.centralizer ({ae6ModelZ} : Set AE6Om),
      conjSub g ae6ModelP ≤ ae6ModelP := by
    intro g hg
    unfold ae6ModelP
    rw [sSup_eq_iSup, conjSub_iSup₂]
    exact iSup₂_le fun J hJ => le_iSup₂_of_le (conjSub g J) (conjSub_mem_twins hg hJ) le_rfl
  refine le_antisymm (key c hc) ?_
  calc ae6ModelP = conjSub c (conjSub c⁻¹ ae6ModelP) := (conjSub_conjSub_inv c _).symm
    _ ≤ conjSub c ae6ModelP := conjSub_mono (key _ (Subgroup.inv_mem _ hc))

theorem ae6Om_not_comm (hSmall : AE6ModelSmall) : ∃ a b : AE6Om, a * b ≠ b * a := by
  obtain ⟨⟨q⟩, -, -, -⟩ := hSmall.1
  refine ⟨(q.symm (QuaternionGroup.a 1) : AE6Om), (q.symm (QuaternionGroup.xa 0) : AE6Om), ?_⟩
  intro h
  have h' : q.symm (QuaternionGroup.a 1) * q.symm (QuaternionGroup.xa 0) =
      q.symm (QuaternionGroup.xa 0) * q.symm (QuaternionGroup.a 1) := Subtype.ext h
  rw [← map_mul, ← map_mul] at h'
  exact absurd (q.symm.injective h') (by decide)

end Model

theorem ae6Om_center (hSmall : AE6ModelSmall) {z : AE6Om} (hz : ∀ g : AE6Om, g * z = z * g) :
    z = 1 := by
  haveI := A6.curtisOmegaT_isSimple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center AE6Om) with h | h
  · have hz' : z ∈ Subgroup.center AE6Om := Subgroup.mem_center_iff.mpr hz
    rw [h] at hz'
    exact Subgroup.mem_bot.mp hz'
  · exfalso
    obtain ⟨a, b, hab⟩ := ae6Om_not_comm hSmall
    have hb : b ∈ Subgroup.center AE6Om := h ▸ Subgroup.mem_top b
    exact hab (Subgroup.mem_center_iff.mp hb a)

section PGrp

variable {Y : Type} [Group Y]

theorem conjSub_ae6P {Ω : Set (Subgroup Y)} (hinv : ConjInvariant Ω) (g s : Y) :
    conjSub g (ae6P Ω s) = ae6P Ω (g * s * g⁻¹) := by
  have key : ∀ (g s : Y), conjSub g (ae6P Ω s) ≤ ae6P Ω (g * s * g⁻¹) := by
    intro g s
    unfold ae6P
    rw [conjSub_iSup₂ g (fun J => J) (ae6Vc Ω s)]
    exact iSup₂_le fun J hJ => le_iSup₂_of_le (conjSub g J)
      ⟨hinv g J hJ.1, A6jB.isUniqueInvolution_conjSub hJ.2 g⟩ le_rfl
  refine le_antisymm (key g s) ?_
  have h := key g⁻¹ (g * s * g⁻¹)
  rw [show g⁻¹ * (g * s * g⁻¹) * g⁻¹⁻¹ = s by group] at h
  calc ae6P Ω (g * s * g⁻¹) = conjSub g (conjSub g⁻¹ (ae6P Ω (g * s * g⁻¹))) :=
        (conjSub_conjSub_inv g _).symm
    _ ≤ conjSub g (ae6P Ω s) := conjSub_mono h

theorem mem_normalizer_ae6P {Ω : Set (Subgroup Y)} (hinv : ConjInvariant Ω) {s c : Y}
    (hc : c ∈ Subgroup.centralizer ({s} : Set Y)) : c ∈ Subgroup.normalizer (ae6P Ω s : Set Y) := by
  rw [mem_normalizer_iff_conjSub_eq, conjSub_ae6P hinv]
  rw [Subgroup.mem_centralizer_singleton_iff] at hc
  rw [hc, mul_inv_cancel_right]

theorem le_ae6P {Ω : Set (Subgroup Y)} {J : Subgroup Y} {s : Y} (hJ : J ∈ Ω)
    (hs : IsUniqueInvolution J s) : J ≤ ae6P Ω s := by
  unfold ae6P
  exact le_iSup₂_of_le J ⟨hJ, hs⟩ le_rfl

theorem ae6P_le_ae6L {Ω : Set (Subgroup Y)} (t τ x : Y) : ae6P Ω t ≤ ae6L Ω t τ x := by
  unfold ae6P ae6L
  exact iSup₂_le fun J hJ => le_iSup₂_of_le J (Or.inl (Or.inl hJ)) le_rfl

end PGrp

section Count

variable {Y : Type} [Group Y] [Finite Y]

theorem natCard_subgroup_eq_ncard {G : Type*} [Group G] (H : Subgroup G) :
    Nat.card H = (H : Set G).ncard := by
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]

theorem card_W_aux {W : Subgroup Y} {t τ : Y} {M : Fin 4 → Subgroup Y} {a r : Fin 4 → Y}
    (hW2 : IsPGroup 2 W) (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (htW : t ∈ W) (ht1 : t ≠ 1)
    (hq : ∀ i, WF.Q8Facts (M i) t) (haM : ∀ i, a i ∈ M i) (haW : ∀ i, a i ∈ W)
    (haa : ∀ i, a i * a i = t) (hrM : ∀ i, r i ∈ M i) (har : ∀ i, a i * r i ≠ r i * a i)
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ M i, ∀ y ∈ M j, x * y = y * x)
    (hWN : ∀ i, W ≤ Subgroup.normalizer (M i : Set Y))
    (hMN : ∀ i, M i ≤ Subgroup.normalizer (W : Set Y)) (hτ : τ = a 0 * a 1 * a 2 * a 3)
    (hsq : ∀ w ∈ W, w * w = 1 ∨ w * w = t ∨ w * w = τ ∨ w * w = t * τ)
    (hv : ∃ v ∈ W, v * v = τ)
    (hCP : ∀ w ∈ W, (∀ i, ∀ x ∈ M i, w * x = x * w) → w = 1 ∨ w = t) :
    Nat.card W = 64 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htt : t * t = 1 := (hq 0).z_sq
  have hcyc : ∀ i, ∀ x ∈ M i, x ∈ W → x = 1 ∨ x = a i ∨ x = t ∨ x = a i * t := fun i x hxM hxW =>
    (hq i).cent_cyc (a i) (haM i) (haa i) x hxM (hWc x hxW (a i) (haW i))
  have hvalM : ∀ w ∈ W, ∀ i, w * r i * w⁻¹ * (r i)⁻¹ ∈ M i := by
    intro w hw i
    have h1 : w * r i * w⁻¹ ∈ M i := (Subgroup.mem_normalizer_iff.mp (hWN i hw) (r i)).mp (hrM i)
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ (hrM i))
  have hvalW : ∀ w ∈ W, ∀ i, w * r i * w⁻¹ * (r i)⁻¹ ∈ W := by
    intro w hw i
    have h1 : r i * w⁻¹ * (r i)⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (hMN i (hrM i)) w⁻¹).mp (Subgroup.inv_mem _ hw)
    have e : w * r i * w⁻¹ * (r i)⁻¹ = w * (r i * w⁻¹ * (r i)⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hw h1
  let d : ↥W →* (Fin 4 → Y) :=
    { toFun := fun w i => (w : Y) * r i * (w : Y)⁻¹ * (r i)⁻¹
      map_one' := by funext i; simp
      map_mul' := by
        intro w w'
        funext i
        have hx' := hvalW w' w'.2 i
        have hx := hvalW w w.2 i
        have hc1 : (w : Y) * ((w' : Y) * r i * (w' : Y)⁻¹ * (r i)⁻¹) =
            ((w' : Y) * r i * (w' : Y)⁻¹ * (r i)⁻¹) * w := hWc _ w.2 _ hx'
        have hc2 : ((w : Y) * r i * (w : Y)⁻¹ * (r i)⁻¹) * ((w' : Y) * r i * (w' : Y)⁻¹ * (r i)⁻¹) =
            ((w' : Y) * r i * (w' : Y)⁻¹ * (r i)⁻¹) * ((w : Y) * r i * (w : Y)⁻¹ * (r i)⁻¹) :=
          hWc _ hx _ hx'
        simp only [Subgroup.coe_mul, Pi.mul_apply]
        rw [hc2]
        calc (w : Y) * w' * r i * ((w : Y) * w')⁻¹ * (r i)⁻¹
            = (w : Y) * ((w' : Y) * r i * (w' : Y)⁻¹ * (r i)⁻¹) * (w : Y)⁻¹ *
                ((w : Y) * r i * (w : Y)⁻¹ * (r i)⁻¹) := by group
          _ = ((w' : Y) * r i * (w' : Y)⁻¹ * (r i)⁻¹) * w * (w : Y)⁻¹ *
                ((w : Y) * r i * (w : Y)⁻¹ * (r i)⁻¹) := by rw [hc1]
          _ = ((w' : Y) * r i * (w' : Y)⁻¹ * (r i)⁻¹) * ((w : Y) * r i * (w : Y)⁻¹ * (r i)⁻¹) := by
                group }
  have hd_apply : ∀ (w : ↥W) i, d w i = (w : Y) * r i * (w : Y)⁻¹ * (r i)⁻¹ := fun _ _ => rfl
  have hda : ∀ j i, d ⟨a j, haW j⟩ i = if i = j then t else 1 := by
    intro j i
    rw [hd_apply]
    split_ifs with hij
    · subst hij
      exact (hq i).comm_eq (a i) (haM i) (r i) (hrM i) (har i)
    · have h := hcomm j i (Ne.symm hij) (a j) (haM j) (r i) (hrM i)
      calc a j * r i * (a j)⁻¹ * (r i)⁻¹ = r i * a j * (a j)⁻¹ * (r i)⁻¹ := by rw [h]
        _ = 1 := by group
  have hdt : d ⟨t, htW⟩ = 1 := by
    funext i
    rw [hd_apply, Pi.one_apply]
    have h := (hq i).z_central (r i) (hrM i)
    show t * r i * t⁻¹ * (r i)⁻¹ = 1
    rw [h]
    group
  have hτW : τ ∈ W := hτ ▸ Subgroup.mul_mem _
    (Subgroup.mul_mem _ (Subgroup.mul_mem _ (haW 0) (haW 1)) (haW 2)) (haW 3)
  have hdτ : d ⟨τ, hτW⟩ = fun _ => t := by
    have e : (⟨τ, hτW⟩ : ↥W) = ⟨a 0, haW 0⟩ * ⟨a 1, haW 1⟩ * ⟨a 2, haW 2⟩ * ⟨a 3, haW 3⟩ :=
      Subtype.ext hτ
    rw [e, map_mul, map_mul, map_mul]
    funext i
    simp only [Pi.mul_apply, hda]
    fin_cases i <;> simp
  have hdsq : ∀ w : ↥W, d w * d w = 1 ∨ d w * d w = fun _ => t := by
    intro w
    rw [← map_mul]
    rcases hsq w w.2 with h | h | h | h
    · left
      have e : w * w = 1 := Subtype.ext h
      rw [e, map_one]
    · left
      have e : w * w = ⟨t, htW⟩ := Subtype.ext h
      rw [e, hdt]
    · right
      have e : w * w = ⟨τ, hτW⟩ := Subtype.ext h
      rw [e, hdτ]
    · right
      have e : w * w = ⟨t, htW⟩ * ⟨τ, hτW⟩ := Subtype.ext h
      rw [e, map_mul, hdt, hdτ, one_mul]
  let g₁ : (Fin 4 → Bool) → (Fin 4 → Y) := fun σ i => if σ i then t else 1
  let g₂ : (Fin 4 → Bool) → (Fin 4 → Y) := fun σ i => if σ i then a i * t else a i
  have hat : ∀ i, a i * t ≠ a i := fun i h => ht1 (by simpa using h)
  have hatat : ∀ i, a i * t * (a i * t) = t := by
    intro i
    have hc := (hq i).z_central (a i) (haM i)
    calc a i * t * (a i * t) = a i * (t * a i) * t := by group
      _ = a i * a i * (t * t) := by rw [hc]; group
      _ = t := by rw [haa, htt, mul_one]
  have hrange : (d.range : Set (Fin 4 → Y)) ⊆ Set.range g₁ ∪ Set.range g₂ := by
    rintro _ ⟨w, rfl⟩
    have hvals : ∀ i, d w i = 1 ∨ d w i = a i ∨ d w i = t ∨ d w i = a i * t := fun i =>
      hcyc i _ (hvalM w w.2 i) (hvalW w w.2 i)
    rcases hdsq w with h | h
    · left
      refine ⟨fun i => decide (d w i = t), ?_⟩
      funext i
      have hi : d w i * d w i = 1 := by simpa using congrFun h i
      rcases hvals i with e | e | e | e
      · simp [g₁, e, Ne.symm ht1]
      · exfalso; rw [e, haa] at hi; exact ht1 hi
      · simp [g₁, e]
      · exfalso; rw [e, hatat] at hi; exact ht1 hi
    · right
      refine ⟨fun i => decide (d w i = a i * t), ?_⟩
      funext i
      have hi : d w i * d w i = t := by simpa using congrFun h i
      rcases hvals i with e | e | e | e
      · exfalso; rw [e, one_mul] at hi; exact ht1 hi.symm
      · simp [g₂, e, (hat i).symm]
      · exfalso; rw [e, htt] at hi; exact ht1 hi.symm
      · simp [g₂, e]
  have hker : ∀ w : ↥W, d w = 1 → (w : Y) = 1 ∨ (w : Y) = t := by
    intro w hw
    apply hCP w w.2
    intro i x hx
    have hri : (w : Y) * r i = r i * w := by
      have h := congrFun hw i
      rw [hd_apply, Pi.one_apply] at h
      calc (w : Y) * r i = ((w : Y) * r i * (w : Y)⁻¹ * (r i)⁻¹) * (r i * w) := by group
        _ = r i * w := by rw [h, one_mul]
    have hai : (w : Y) * a i = a i * w := hWc _ w.2 _ (haW i)
    obtain ⟨k, -, j, -, rfl⟩ := (hq i).gen (a i) (haM i) (r i) (hrM i) (har i) x hx
    have c1 : Commute (w : Y) (a i ^ k) := (Commute.pow_right hai k)
    have c2 : Commute (w : Y) (r i ^ j) := (Commute.pow_right hri j)
    exact (c1.mul_right c2).eq
  have hkercard : Nat.card d.ker = 2 := by
    have hset : (d.ker : Set ↥W) = {1, ⟨t, htW⟩} := by
      ext w
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · intro hw
        rcases hker w hw with h | h
        · left; exact Subtype.ext h
        · right; exact Subtype.ext h
      · rintro (rfl | rfl)
        · exact map_one d
        · exact hdt
    rw [natCard_subgroup_eq_ncard, hset]
    refine Set.ncard_pair fun h => ht1 ?_
    exact (congrArg Subtype.val h).symm
  have hg₁inj : Function.Injective g₁ := by
    intro σ σ' h
    funext i
    have hi := congrFun h i
    simp only [g₁] at hi
    cases hσ : σ i <;> cases hσ' : σ' i <;> simp only [hσ, hσ'] at hi ⊢ <;>
      first | rfl | exact absurd hi (Ne.symm ht1) | exact absurd hi ht1
  have hg₂inj : Function.Injective g₂ := by
    intro σ σ' h
    funext i
    have hi := congrFun h i
    simp only [g₂] at hi
    cases hσ : σ i <;> cases hσ' : σ' i <;> simp only [hσ, hσ'] at hi ⊢ <;>
      first | rfl | exact absurd hi (Ne.symm (hat i)) | exact absurd hi (hat i)
  have hcard16 : Nat.card (Fin 4 → Bool) = 16 := by
    rw [Nat.card_fun]; simp
  have hT : (Set.range g₁).ncard = 16 := by rw [Set.ncard_range_of_injective hg₁inj, hcard16]
  have hT₂ : (Set.range g₂).ncard = 16 := by rw [Set.ncard_range_of_injective hg₂inj, hcard16]
  have hup : Nat.card d.range ≤ 32 := by
    rw [natCard_subgroup_eq_ncard]
    calc (d.range : Set (Fin 4 → Y)).ncard ≤ (Set.range g₁ ∪ Set.range g₂).ncard :=
          Set.ncard_le_ncard hrange
      _ ≤ (Set.range g₁).ncard + (Set.range g₂).ncard := Set.ncard_union_le _ _
      _ = 32 := by rw [hT, hT₂]
  have hTd : Set.range g₁ ⊆ (d.range : Set (Fin 4 → Y)) := by
    rintro _ ⟨σ, rfl⟩
    have he : ∀ j, (fun i => if i = j then t else 1) ∈ d.range := fun j =>
      ⟨⟨a j, haW j⟩, funext (hda j)⟩
    have hf : ∀ j, (if σ j then (fun i => if i = j then t else 1) else 1) ∈ d.range := by
      intro j
      split_ifs
      · exact he j
      · exact d.range.one_mem
    have hfac : g₁ σ = (if σ 0 then (fun i => if i = 0 then t else 1) else 1) *
        (if σ 1 then (fun i => if i = 1 then t else 1) else 1) *
        (if σ 2 then (fun i => if i = 2 then t else 1) else 1) *
        (if σ 3 then (fun i => if i = 3 then t else 1) else 1) := by
      funext i
      fin_cases i <;> simp [g₁, ite_apply]
    show g₁ σ ∈ d.range
    rw [hfac]
    exact d.range.mul_mem (d.range.mul_mem (d.range.mul_mem (hf 0) (hf 1)) (hf 2)) (hf 3)
  obtain ⟨v, hvW, hvv⟩ := hv
  have hdv : d ⟨v, hvW⟩ * d ⟨v, hvW⟩ = fun _ => t := by
    rw [← map_mul]
    have e : (⟨v, hvW⟩ : ↥W) * ⟨v, hvW⟩ = ⟨τ, hτW⟩ := Subtype.ext hvv
    rw [e, hdτ]
  have hdvT : d ⟨v, hvW⟩ ∉ Set.range g₁ := by
    rintro ⟨σ, hσ⟩
    have h0 := congrFun hdv 0
    rw [← hσ] at h0
    simp only [Pi.mul_apply, g₁] at h0
    split_ifs at h0
    · rw [htt] at h0; exact ht1 h0.symm
    · rw [one_mul] at h0; exact ht1 h0.symm
  have hlow : 17 ≤ Nat.card d.range := by
    rw [natCard_subgroup_eq_ncard]
    have hsub : insert (d ⟨v, hvW⟩) (Set.range g₁) ⊆ (d.range : Set (Fin 4 → Y)) :=
      Set.insert_subset ⟨_, rfl⟩ hTd
    calc 17 = (insert (d ⟨v, hvW⟩) (Set.range g₁)).ncard := by
          rw [Set.ncard_insert_of_notMem hdvT, hT]
      _ ≤ (d.range : Set (Fin 4 → Y)).ncard := Set.ncard_le_ncard hsub
  have hWcard : Nat.card W = 2 * Nat.card d.range := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup d.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange d).toEquiv, hkercard, mul_comm]
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hW2
  have h1 : 34 ≤ 2 ^ k := by rw [← hk, hWcard]; omega
  have h2 : 2 ^ k ≤ 64 := by rw [← hk, hWcard]; omega
  have hk6 : k = 6 := by
    have hle : k ≤ 6 := by
      by_contra h
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show 7 ≤ k by omega)
      norm_num at this
      omega
    interval_cases k <;> first | rfl | (norm_num at h1) | (norm_num at h2)
  rw [hk, hk6]
  norm_num

theorem E4_mul {G : Type*} [Group G] {t τ x x' : G} (htt : t * t = 1) (hττ : τ * τ = 1)
    (hc : τ * t = t * τ) (hx : x = 1 ∨ x = t ∨ x = τ ∨ x = t * τ)
    (hx' : x' = 1 ∨ x' = t ∨ x' = τ ∨ x' = t * τ) :
    x * x' = 1 ∨ x * x' = t ∨ x * x' = τ ∨ x * x' = t * τ := by
  have h1 : ∀ z : G, t * (t * z) = z := fun z => by rw [← mul_assoc, htt, one_mul]
  have h2 : ∀ z : G, τ * (τ * z) = z := fun z => by rw [← mul_assoc, hττ, one_mul]
  have h3 : ∀ z : G, τ * (t * z) = t * (τ * z) := fun z => by rw [← mul_assoc, hc, mul_assoc]
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hx' with rfl | rfl | rfl | rfl <;>
    simp only [mul_assoc, htt, hττ, hc, h1, h2, h3, mul_one, one_mul, true_or, or_true]

theorem E4_sq {G : Type*} [Group G] {t τ x : G} (htt : t * t = 1) (hττ : τ * τ = 1)
    (hc : τ * t = t * τ) (hx : x = 1 ∨ x = t ∨ x = τ ∨ x = t * τ) : x * x = 1 := by
  rcases hx with rfl | rfl | rfl | rfl
  · exact mul_one 1
  · exact htt
  · exact hττ
  · calc t * τ * (t * τ) = t * (τ * t) * τ := by group
      _ = 1 := by rw [hc, ← mul_assoc, htt, one_mul, hττ]

end Count

section Transport

variable {Y : Type} [Group Y] {Hε : Subgroup Y}

theorem mem_centralizer_iff_conj {J : Subgroup Y} {c : Y} :
    c ∈ Subgroup.centralizer (J : Set Y) ↔ ∀ p ∈ J, c * p * c⁻¹ = p := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h p hp
    rw [← h p hp, mul_inv_cancel_right]
  · intro h p hp
    calc p * c = (c * p * c⁻¹) * c := by rw [h p hp]
      _ = c * p := by group

theorem conjSub_iSup {ι : Sort*} (g : Y) (B : ι → Subgroup Y) :
    conjSub g (⨆ i, B i) = ⨆ i, conjSub g (B i) := by
  unfold conjSub
  exact Subgroup.map_iSup _ _

@[expose] noncomputable def ae6Emb (e : ↥Hε ≃* AE6Om) : AE6Om →* Y :=
  Hε.subtype.comp e.symm.toMonoidHom

theorem ae6Emb_apply (e : ↥Hε ≃* AE6Om) (a : AE6Om) : ae6Emb e a = ((e.symm a : ↥Hε) : Y) := rfl

theorem ae6Emb_injective (e : ↥Hε ≃* AE6Om) : Function.Injective (ae6Emb e) :=
  Hε.subtype_injective.comp e.symm.injective

theorem ae6Emb_mem (e : ↥Hε ≃* AE6Om) (a : AE6Om) : ae6Emb e a ∈ Hε := (e.symm a).2

theorem ae6Emb_e (e : ↥Hε ≃* AE6Om) (g : ↥Hε) : ae6Emb e (e g) = g := by
  rw [ae6Emb_apply, MulEquiv.symm_apply_apply]

theorem ae6Emb_range (e : ↥Hε ≃* AE6Om) : (ae6Emb e).range = Hε := by
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    exact ae6Emb_mem e a
  · intro hy
    exact ⟨e ⟨y, hy⟩, ae6Emb_e e ⟨y, hy⟩⟩

theorem ae6Emb_trans_conj (e : ↥Hε ≃* AE6Om) (c a : AE6Om) :
    ae6Emb (e.trans (MulAut.conj c)) a = ae6Emb e (c⁻¹ * a * c) := by
  simp only [ae6Emb_apply, MulEquiv.symm_trans_apply, MulAut.conj_symm_apply]

theorem map_ae6Emb_trans_conj (e : ↥Hε ≃* AE6Om) (c : AE6Om) (B : Subgroup AE6Om) :
    B.map (ae6Emb (e.trans (MulAut.conj c))) = (conjSub c⁻¹ B).map (ae6Emb e) := by
  ext y
  simp only [Subgroup.mem_map, ae6Emb_trans_conj]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨c⁻¹ * a * c, by simpa using conj_mem_conjSub (n := c⁻¹) ha, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    rw [mem_conjSub_iff] at hb
    refine ⟨c * b * c⁻¹, by simpa using hb, ?_⟩
    congr 1
    group

structure AE6TranspP (e : ↥Hε ≃* AE6Om) (t : Y) (V : Set (Subgroup Y)) (P : Subgroup Y) : Prop where
  z_eq : ae6Emb e ae6ModelZ = t
  twins_iff : ∀ J, J ∈ V ↔ ∃ J₀ ∈ ae6ModelTwins, J₀.map (ae6Emb e) = J
  P_eq : ae6ModelP.map (ae6Emb e) = P

theorem AE6TranspP.move {e : ↥Hε ≃* AE6Om} {t : Y} {V : Set (Subgroup Y)} {P : Subgroup Y}
    (hT : AE6TranspP e t V P) {c : AE6Om}
    (hc : c ∈ Subgroup.centralizer ({ae6ModelZ} : Set AE6Om)) :
    AE6TranspP (e.trans (MulAut.conj c⁻¹)) t V P ∧ ∀ B : Subgroup AE6Om,
      B.map (ae6Emb (e.trans (MulAut.conj c⁻¹))) = (conjSub c B).map (ae6Emb e) := by
  have hB : ∀ B : Subgroup AE6Om,
      B.map (ae6Emb (e.trans (MulAut.conj c⁻¹))) = (conjSub c B).map (ae6Emb e) := by
    intro B
    rw [map_ae6Emb_trans_conj, inv_inv]
  have hci : c⁻¹ ∈ Subgroup.centralizer ({ae6ModelZ} : Set AE6Om) := Subgroup.inv_mem _ hc
  refine ⟨⟨?_, ?_, ?_⟩, hB⟩
  · rw [ae6Emb_trans_conj, inv_inv]
    rw [Subgroup.mem_centralizer_singleton_iff] at hc
    rw [hc, mul_inv_cancel_right, hT.z_eq]
  · intro J
    rw [hT.twins_iff]
    constructor
    · rintro ⟨J₀, hJ₀, rfl⟩
      refine ⟨conjSub c⁻¹ J₀, conjSub_mem_twins hci hJ₀, ?_⟩
      rw [hB, conjSub_conjSub_inv]
    · rintro ⟨J₀, hJ₀, rfl⟩
      exact ⟨conjSub c J₀, conjSub_mem_twins hc hJ₀, (hB J₀).symm⟩
  · rw [hB, conjSub_ae6ModelP hc, hT.P_eq]

noncomputable def ae6Rho {P N : Subgroup Y} (e : ↥Hε ≃* AE6Om) (hP : ae6ModelP.map (ae6Emb e) = P)
    (hN : N ≤ Subgroup.normalizer (P : Set Y)) : ↥N →* MulAut ↥ae6ModelP :=
  (MulAut.congr ((ae6ModelP.equivMapOfInjective (ae6Emb e) (ae6Emb_injective e)).trans
    (MulEquiv.subgroupCongr hP)).symm).toMonoidHom.comp
    (P.normalizerMonoidHom.comp (Subgroup.inclusion hN))

theorem ae6Rho_apply {P N : Subgroup Y} (e : ↥Hε ≃* AE6Om) (hP : ae6ModelP.map (ae6Emb e) = P)
    (hN : N ≤ Subgroup.normalizer (P : Set Y)) (c : ↥N) (p : ↥ae6ModelP) :
    ae6Emb e ((ae6Rho e hP hN c p : ↥ae6ModelP) : AE6Om) = (c : Y) * ae6Emb e p * (c : Y)⁻¹ := by
  set φ := (ae6ModelP.equivMapOfInjective (ae6Emb e) (ae6Emb_injective e)).trans
    (MulEquiv.subgroupCongr hP) with hφdef
  have hφ : ∀ q : ↥ae6ModelP, ((φ q : ↥P) : Y) = ae6Emb e q := by
    intro q
    rw [hφdef, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
      Subgroup.coe_equivMapOfInjective_apply]
  have hφs : ∀ r : ↥P, ae6Emb e (φ.symm r : AE6Om) = r := by
    intro r
    have h := hφ (φ.symm r)
    rw [MulEquiv.apply_symm_apply] at h
    exact h.symm
  show ae6Emb e (((MulAut.congr φ.symm) (P.normalizerMonoidHom (Subgroup.inclusion hN c)) p :
    ↥ae6ModelP) : AE6Om) = _
  rw [MulAut.congr_apply, MulEquiv.symm_symm, MulEquiv.trans_apply, MulEquiv.trans_apply, hφs,
    Subgroup.normalizerMonoidHom_apply_apply_coe, hφ]
  rfl

theorem step1 (hC1 : AE6ModelC1') (hC2 : AE6ModelC2) {Ω : Set (Subgroup Y)} (hinv : ConjInvariant Ω)
    {e : ↥Hε ≃* AE6Om} {t : Y} {V : Set (Subgroup Y)} (hT : AE6TranspP e t V (ae6P Ω t)) {x : Y}
    (hxP : ∀ p ∈ ae6P Ω t, x * p = p * x) :
    ∃ ε : Y, (ε = 1 ∨ ε = t) ∧ ∀ g ∈ Hε, x * g * x⁻¹ = ε * g * ε⁻¹ := by
  have hfi := ae6Emb_injective e
  have hC1' : (⨆ (h : AE6Om) (_ : h⁻¹ * ae6ModelZ * h ∈ ae6ModelP), conjSub h⁻¹ ae6ModelP) = ⊤ :=
    hC1
  have hHε : (⨆ (h₀ : AE6Om) (_ : h₀⁻¹ * ae6ModelZ * h₀ ∈ ae6ModelP),
      conjSub (ae6Emb e h₀)⁻¹ (ae6P Ω t)) = Hε := by
    have h1 := congrArg (Subgroup.map (ae6Emb e)) hC1'
    rw [← MonoidHom.range_eq_map, ae6Emb_range] at h1
    refine Eq.trans ?_ h1
    simp only [Subgroup.map_iSup, map_conjSub_hom, map_inv, hT.P_eq]
  have hnorm : ∀ h₀ : AE6Om, h₀⁻¹ * ae6ModelZ * h₀ ∈ ae6ModelP →
      conjSub x (conjSub (ae6Emb e h₀)⁻¹ (ae6P Ω t)) = conjSub (ae6Emb e h₀)⁻¹ (ae6P Ω t) := by
    intro h₀ hh₀
    have hs : (ae6Emb e h₀)⁻¹ * t * ae6Emb e h₀ ∈ ae6P Ω t := by
      have h1 : ae6Emb e (h₀⁻¹ * ae6ModelZ * h₀) ∈ ae6P Ω t := by
        rw [← hT.P_eq]
        exact Subgroup.mem_map_of_mem _ hh₀
      rwa [map_mul, map_mul, map_inv, hT.z_eq] at h1
    rw [conjSub_ae6P hinv, inv_inv, ← mem_normalizer_iff_conjSub_eq]
    apply mem_normalizer_ae6P hinv
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hxP _ hs
  have hxN : x ∈ Subgroup.normalizer (Hε : Set Y) := by
    rw [mem_normalizer_iff_conjSub_eq, ← hHε, conjSub_iSup]
    refine iSup_congr fun h₀ => ?_
    rw [conjSub_iSup]
    exact iSup_congr fun hh₀ => hnorm h₀ hh₀
  let ψ : MulAut AE6Om := MulAut.congr e (Hε.normalizerMonoidHom ⟨x, hxN⟩)
  have hψ : ∀ a, ae6Emb e (ψ a) = x * ae6Emb e a * x⁻¹ := by
    intro a
    show ((e.symm (MulAut.congr e (Hε.normalizerMonoidHom ⟨x, hxN⟩) a) : ↥Hε) : Y) = _
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
      Subgroup.normalizerMonoidHom_apply_apply_coe]
    rfl
  have hfix : ∀ p ∈ ae6ModelP, ψ p = p := by
    intro p hp
    apply hfi
    rw [hψ]
    have hfp : ae6Emb e p ∈ ae6P Ω t := by
      rw [← hT.P_eq]
      exact Subgroup.mem_map_of_mem _ hp
    rw [hxP _ hfp, mul_inv_cancel_right]
  rcases hC2 ψ hfix with h | h
  · refine ⟨1, Or.inl rfl, fun g hg => ?_⟩
    obtain ⟨a, rfl⟩ : ∃ a, ae6Emb e a = g := ⟨e ⟨g, hg⟩, ae6Emb_e e ⟨g, hg⟩⟩
    rw [← hψ, h, MulAut.one_apply]
    group
  · refine ⟨t, Or.inr rfl, fun g hg => ?_⟩
    obtain ⟨a, rfl⟩ : ∃ a, ae6Emb e a = g := ⟨e ⟨g, hg⟩, ae6Emb_e e ⟨g, hg⟩⟩
    rw [← hψ, h, MulAut.conj_apply, map_mul, map_mul, map_inv, hT.z_eq]

end Transport

section Center


variable {Y : Type} [Group Y] {Hε : Subgroup Y}

theorem center_eq_one (hSmall : AE6ModelSmall) (e : ↥Hε ≃* AE6Om) {z : Y} (hz : z ∈ Hε)
    (hc : ∀ g ∈ Hε, z * g = g * z) : z = 1 := by
  have h0 : e ⟨z, hz⟩ = 1 := by
    apply ae6Om_center hSmall
    intro a
    obtain ⟨g, rfl⟩ := e.surjective a
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc g g.2).symm
  have : (⟨z, hz⟩ : ↥Hε) = 1 := e.injective (by rw [h0, map_one])
  exact congrArg Subtype.val this

theorem cent_P_transp (hSmall : AE6ModelSmall) (hC2 : AE6ModelC2) {e : ↥Hε ≃* AE6Om} {t : Y}
    {V : Set (Subgroup Y)} {P : Subgroup Y} (hT : AE6TranspP e t V P) {w : Y} (hw : w ∈ Hε)
    (hc : ∀ p ∈ P, w * p = p * w) : w = 1 ∨ w = t := by
  have hfi := ae6Emb_injective e
  have hfw : ae6Emb e (e ⟨w, hw⟩) = w := ae6Emb_e e ⟨w, hw⟩
  have hfix : ∀ p ∈ ae6ModelP, MulAut.conj (e ⟨w, hw⟩) p = p := by
    intro p hp
    rw [MulAut.conj_apply]
    apply hfi
    have hfp : ae6Emb e p ∈ P := by
      rw [← hT.P_eq]
      exact Subgroup.mem_map_of_mem _ hp
    rw [map_mul, map_mul, map_inv, hfw]
    calc w * ae6Emb e p * w⁻¹ = ae6Emb e p * w * w⁻¹ := by rw [hc _ hfp]
      _ = ae6Emb e p := mul_inv_cancel_right _ _
  have hcent : ∀ x : AE6Om, (∀ g : AE6Om, MulAut.conj x g = g) → x = 1 := by
    intro x hx
    apply ae6Om_center hSmall
    intro g
    have h := hx g
    rw [MulAut.conj_apply] at h
    calc g * x = x * g * x⁻¹ * x := by rw [h]
      _ = x * g := by group
  rcases hC2 _ hfix with h | h
  · left
    have h1 : e ⟨w, hw⟩ = 1 := hcent _ fun g => by rw [h]; rfl
    rw [← hfw, h1, map_one]
  · right
    have h1 : ae6ModelZ⁻¹ * e ⟨w, hw⟩ = 1 := by
      apply hcent
      intro g
      have hg := congrArg (fun φ : MulAut AE6Om => φ g) h
      simp only [MulAut.conj_apply] at hg
      rw [MulAut.conj_apply]
      calc ae6ModelZ⁻¹ * e ⟨w, hw⟩ * g * (ae6ModelZ⁻¹ * e ⟨w, hw⟩)⁻¹ =
          ae6ModelZ⁻¹ * (e ⟨w, hw⟩ * g * (e ⟨w, hw⟩)⁻¹) * ae6ModelZ := by group
        _ = g := by rw [hg]; group
    have h2 : e ⟨w, hw⟩ = ae6ModelZ := by
      calc e ⟨w, hw⟩ = ae6ModelZ * (ae6ModelZ⁻¹ * e ⟨w, hw⟩) := by group
        _ = ae6ModelZ := by rw [h1, mul_one]
    rw [← hfw, h2, hT.z_eq]

end Center

variable {n : ℕ}


local notation "Ω[" R "]" => CoreAssembly.conjClass (tightCore R)

@[expose] def V3AE6NoWt1 (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y) (K₄ W : Subgroup Y) (a₁ a₂ a₃ a₄ y : Y),
    AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W → AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y →
      ∀ c ∈ Subgroup.centralizer ({t} : Set Y), IsPGroup 3 (Subgroup.zpowers c) →
        (∀ J ∈ twinSet Ω[R] K, c ∈ Subgroup.normalizer (J : Set Y)) →
          Set.ncard {J | J ∈ twinSet Ω[R] K ∧ ∃ p ∈ J, c * p * c⁻¹ ≠ p} ≠ 1

section Datum

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y} {a₁ a₂ a₃ a₄ y : Y}

theorem twinSet_eq_ae6Vc (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) :
    twinSet Ω[R] K = ae6Vc Ω[R] t := by
  have hz := H.ex.1.datum.hz
  ext J
  constructor
  · intro hJ
    exact ⟨hJ.1, isUniqueInvolution_of_mem_twinSet hz hJ⟩
  · rintro ⟨hJ, hJt⟩
    exact ⟨hJ, t, hz, hJt⟩

theorem t_mem_W (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) : t ∈ W :=
  H.ex.1.datum.sq₁ ▸ W.mul_mem H.hu₁ H.hu₁

theorem W_comm (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x :=
  Q3.Q3T6.abelian_of_mem_WSet3 (CoreData.of_S H.ex.1.perp.core).hyp H.hW

theorem W_le_cent (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) :
    W ≤ Subgroup.centralizer ({t} : Set Y) := fun w hw => by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact W_comm H w hw t (t_mem_W H)

theorem q8Facts_twin (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) {J : Subgroup Y}
    (hJ : J ∈ twinSet Ω[R] K) : WF.Q8Facts J t := by
  obtain ⟨e⟩ := members_q8_of_isPGroup H.ex.1.perp H.ex.2.2.2.1 J hJ.1
  exact WF.q8Facts_of_iso (isUniqueInvolution_of_mem_twinSet H.ex.1.datum.hz hJ) e

theorem twin_comm (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) {J J' : Subgroup Y}
    (hJ : J ∈ twinSet Ω[R] K) (hJ' : J' ∈ twinSet Ω[R] K) (hne : J ≠ J') :
    ∀ x ∈ J, ∀ y ∈ J', x * y = y * x := by
  have hz := H.ex.1.datum.hz
  intro x hx y hy
  have h1 := A7T22.le_trivialOnQuot_of_twin (CoreData.of_S H.ex.1.perp.core).hyp hJ.1 hJ'.1 hne
    (isUniqueInvolution_of_mem_twinSet hz hJ) (isUniqueInvolution_of_mem_twinSet hz hJ') hx
  exact commute_of_trivialOnQuot (H.ex.2.2.2.1 J' hJ'.1) h1 hy

theorem W_le_normalizer_twin (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) {J : Subgroup Y}
    (hJ : J ∈ twinSet Ω[R] K) : W ≤ Subgroup.normalizer (J : Set Y) := by
  have hΩ : HypOmegaGen Ω[R] := (CoreData.of_S H.ex.1.perp.core).hyp
  have hJt := isUniqueInvolution_of_mem_twinSet H.ex.1.datum.hz hJ
  have hWc := W_le_cent H
  obtain ⟨η, ⟨S₀, hηS₀, -⟩, hWη⟩ := H.hW
  have hUW : ∀ U ∈ η, U ≤ W := fun U hU => hWη ▸ le_iSup₂_of_le U hU le_rfl
  rw [hWη]
  refine iSup₂_le fun U hU => ?_
  have hU' : U ∈ USet Ω[R] := (hηS₀.1 hU).1
  obtain ⟨R₁, -, J₁, hJ₁, hRJ₁, hUR, -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hU'
  have hUJ₁ : U ≤ J₁ := hUR.trans hRJ₁.1
  by_cases hJJ₁ : J = J₁
  · subst hJJ₁
    exact hUJ₁.trans Subgroup.le_normalizer
  · exact Sec6Gen.le_normalizer_of_le_centralizer hΩ hJ.1 hJ₁ hJJ₁ hJt hUJ₁
      (Sec6Gen.isPGroup_of_mem_USet hΩ hU') (by omega) ((hUW U hU).trans hWc)

theorem card_twin_inf_W (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) {J : Subgroup Y}
    (hJ : J ∈ twinSet Ω[R] K) : Nat.card ↥(J ⊓ W) = 4 := by
  have hP := (CoreData.of_S H.ex.1.perp.core).partIHypG
  have h2g := H.ex.2.2.2.1
  have hJD : J ∈ DSet Ω[R] W := twin_mem_DSet hP h2g H.hW (t_mem_W H) hJ.1
    (isUniqueInvolution_of_mem_twinSet H.ex.1.datum.hz hJ)
  have hJsyl : IsSylow2In J J := ⟨le_rfl, h2g J hJ.1, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
  obtain ⟨-, -, -, -, h2⟩ := Q3CL.Thompson.inf_W_of_mem_D H.ex.1.datum.hyp H.hW hJD hJ.1 hJsyl
  have h8 : Nat.card J = 8 := (A6Gen.q8Omega_of_hyp H).card J hJ.1
  omega

theorem exists_conj_t (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) {J : Subgroup Y} (hJ : J ∈ Ω[R])
    {z : Y} (hz : IsUniqueInvolution J z) : ∃ g : Y, g * t * g⁻¹ = z ∧ conjSub g K = J := by
  obtain ⟨g₁, hg₁⟩ := hJ
  obtain ⟨g₂, hg₂⟩ := H.ex.1.datum.mem
  have hg₁' : conjSub g₁ (tightCore R) = J := hg₁
  have hg₂' : conjSub g₂ (tightCore R) = K := hg₂
  have hJK : conjSub (g₁ * g₂⁻¹) K = J := by
    rw [← hg₂', ← conjSub_mul, inv_mul_cancel_right, hg₁']
  refine ⟨g₁ * g₂⁻¹, ?_, hJK⟩
  have h1 := A6jB.isUniqueInvolution_conjSub H.ex.1.datum.hz (g₁ * g₂⁻¹)
  rw [hJK] at h1
  exact h1.eq hz

theorem tau_mem_W (fr : AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y) : y * t * y⁻¹ ∈ W := by
  rw [fr.hy]
  exact W.mul_mem (W.mul_mem (W.mul_mem fr.h₁.2 fr.h₂.2) fr.h₃.2) fr.h₄.2

theorem sq_mem_W (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (fr : AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y) :
    ∀ w ∈ W, w * w = 1 ∨ w * w = t ∨ w * w = y * t * y⁻¹ ∨ w * w = t * (y * t * y⁻¹) := by
  have hΩ : HypOmegaGen Ω[R] := (CoreData.of_S H.ex.1.perp.core).hyp
  have hab := W_comm H
  have htW := t_mem_W H
  have hτW := tau_mem_W fr
  have htt : t * t = 1 := H.ex.1.datum.hz.sq
  have hττ : (y * t * y⁻¹) * (y * t * y⁻¹) = 1 := by
    calc (y * t * y⁻¹) * (y * t * y⁻¹) = y * (t * t) * y⁻¹ := by group
      _ = 1 := by rw [htt]; group
  have hτt : (y * t * y⁻¹) * t = t * (y * t * y⁻¹) := hab _ hτW _ htW
  let Q : Subgroup Y :=
    { carrier := {w | w ∈ W ∧ (w * w = 1 ∨ w * w = t ∨ w * w = y * t * y⁻¹ ∨
        w * w = t * (y * t * y⁻¹))}
      mul_mem' := by
        rintro w w' ⟨hw, hw2⟩ ⟨hw', hw'2⟩
        refine ⟨W.mul_mem hw hw', ?_⟩
        have e : w * w' * (w * w') = (w * w) * (w' * w') := by
          calc w * w' * (w * w') = w * (w' * w) * w' := by group
            _ = w * (w * w') * w' := by rw [hab w' hw' w hw]
            _ = (w * w) * (w' * w') := by group
        rw [e]
        exact E4_mul htt hττ hτt hw2 hw'2
      one_mem' := ⟨W.one_mem, Or.inl (mul_one 1)⟩
      inv_mem' := by
        rintro w ⟨hw, hw2⟩
        refine ⟨W.inv_mem hw, ?_⟩
        have e : w⁻¹ * w⁻¹ = (w * w)⁻¹ := by group
        rw [e, inv_eq_of_mul_eq_one_right (E4_sq htt hττ hτt hw2)]
        exact hw2 }
  obtain ⟨η, ⟨S₀, hηS₀, -⟩, hWη⟩ := H.hW
  have hUW : ∀ U ∈ η, U ≤ W := fun U hU => hWη ▸ le_iSup₂_of_le U hU le_rfl
  have hle : (⨆ U ∈ η, U) ≤ Q := by
    refine iSup₂_le fun U hU x hx => ?_
    have hU' : U ∈ USet Ω[R] := (hηS₀.1 hU).1
    obtain ⟨J₁, hJ₁, hUJ₁⟩ := Sec6Gen.exists_member_of_mem_USet hΩ hU'
    obtain ⟨z₁, hz₁⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ₁
    obtain ⟨e₁⟩ := members_q8_of_isPGroup H.ex.1.perp H.ex.2.2.2.1 J₁ hJ₁
    have hq₁ := WF.q8Facts_of_iso hz₁ e₁
    have hxW := hUW U hU hx
    refine ⟨hxW, ?_⟩
    rcases hq₁.sq_cases x (hUJ₁ hx) with h | h
    · exact Or.inl h
    · right
      obtain ⟨g, hg, -⟩ := exists_conj_t H hJ₁ hz₁
      have hz₁W : z₁ ∈ W := h ▸ W.mul_mem hxW hxW
      rw [h]
      exact A6Wt.mem_tG_W H fr hz₁W hg
  intro w hw
  have hwQ : w ∈ Q := hle (hWη ▸ hw)
  exact hwQ.2

theorem exists_sq_tau (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (fr : AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y) : ∃ v ∈ W, v * v = y * t * y⁻¹ := by
  have hStd := H.ex.1
  have hd := hStd.datum
  have hC := CoreData.of_S hStd.perp.core
  have hΩ : HypOmegaGen Ω[R] := hC.hyp
  have hP := hC.partIHypG
  have hQ8 := A6Gen.q8Omega_of_hyp H
  have h2g : ∀ J ∈ Ω[R], IsPGroup 2 ↥J := H.ex.2.2.2.1
  have htW := t_mem_W H
  have hτW := tau_mem_W fr
  have htr : ∀ K₁ ∈ Ω[R], ∀ J ∈ Ω[R], ∃ x : Y, conjSub x K₁ = J := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact ⟨b * a⁻¹, by rw [conjSub_mul, conjSub_inv_conjSub]⟩
  have hnab : ¬ ∀ x y : ↥(muGroup Ω[R] W), x * y = y * x := fun hc =>
    TL4.not_comm_of_muIsoWylD4_gen (hStd.wyl W H.hW) fun x hx y hy =>
      congrArg Subtype.val (hc ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨S₀, hWS₀, hWC, -⟩ := A6Gen.exists_weaklyClosed_conj_of_nonab hP htr H.hW hnab
  have hWab : ∀ {v : Y}, v ∈ W → v ∈ Subgroup.centralizer (W : Set Y) := fun hv =>
    Subgroup.mem_centralizer_iff.mpr fun x hx =>
      Q3CL.Thompson.commutes_of_mem_WSet hP.hyp H.hW x hx _ hv
  obtain ⟨m, hmN, hm⟩ := Sec7.control_centralizer_of_weaklyClosed
    (S₀.isPGroup'.to_le hWS₀) hWC (hWab htW) (g := y) (hWab hτW)
  have hJΩ : conjSub m K ∈ Ω[R] := hΩ.conjInvariant m K hd.mem
  have hJz : IsUniqueInvolution (conjSub m K) (y * t * y⁻¹) := by
    have := A6jB.isUniqueInvolution_conjSub hd.hz m
    rwa [hm] at this
  have hJD : conjSub m K ∈ DSet Ω[R] W := by
    have := hQ8.conjSub_mem_DSet H.hK m
    rwa [mem_normalizer_iff_conjSub_eq.mp hmN] at this
  obtain ⟨e⟩ := members_q8_of_isPGroup hStd.perp h2g _ hJΩ
  obtain ⟨v, -, hvW, hvv⟩ := WF.exists_gen_sq hΩ H.hW hJΩ hJD (h2g _ hJΩ) (WF.q8Facts_of_iso hJz e)
  exact ⟨v, hvW, hvv⟩

theorem card_W (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (fr : AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y)
    (hCP : ∀ w ∈ W, (∀ p ∈ ae6P Ω[R] t, w * p = p * w) → w = 1 ∨ w = t) : Nat.card W = 64 := by
  classical
  have hStd := H.ex.1
  have hd := hStd.datum
  have hF := H.ex.2.1
  have hP := (CoreData.of_S hStd.perp.core).partIHypG
  have h2g := H.ex.2.2.2.1
  have htW := t_mem_W H
  set M : Fin 4 → Subgroup Y := ![K, K', K₃, K₄] with hM
  set a : Fin 4 → Y := ![a₁, a₂, a₃, a₄] with ha
  have hMtw : ∀ i, M i ∈ twinSet Ω[R] K := by
    intro i
    fin_cases i
    exacts [mem_twinSet_self hd.mem hd.hz, hd.hK', hd.hK₃, hF.1]
  have hinj : Function.Injective M := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [hM] at hij ⊢ <;>
      first
      | exact (hd.hne hij.symm).elim
      | exact (hd.hne hij).elim
      | exact (hd.hK₃K hij.symm).elim
      | exact (hd.hK₃K hij).elim
      | exact (hd.hK₃K' hij.symm).elim
      | exact (hd.hK₃K' hij).elim
      | exact (hF.2.1 hij.symm).elim
      | exact (hF.2.1 hij).elim
      | exact (hF.2.2.1 hij.symm).elim
      | exact (hF.2.2.1 hij).elim
      | exact (hF.2.2.2.1 hij.symm).elim
      | exact (hF.2.2.2.1 hij).elim
  have haM : ∀ i, a i ∈ M i ∧ a i ∈ W ∧ orderOf (a i) = 4 := by
    intro i
    fin_cases i
    exacts [⟨fr.h₁.1, fr.h₁.2, fr.o₁⟩, ⟨fr.h₂.1, fr.h₂.2, fr.o₂⟩, ⟨fr.h₃.1, fr.h₃.2, fr.o₃⟩,
      ⟨fr.h₄.1, fr.h₄.2, fr.o₄⟩]
  have hzM : ∀ i, IsUniqueInvolution (M i) t := fun i =>
    isUniqueInvolution_of_mem_twinSet hd.hz (hMtw i)
  have haa : ∀ i, a i * a i = t := fun i =>
    Asc77.sq_eq_of_orderOf_four (hzM i) (haM i).1 (haM i).2.2
  have ht1 : t ≠ 1 := hd.hz.ne_one
  have hr : ∀ i, ∃ r ∈ M i, a i * r ≠ r * a i := by
    intro i
    have h1 : a i ≠ 1 := fun h => ht1 (by rw [← haa i, h, mul_one])
    have h2 : a i ≠ t := fun h => ht1 (by
      have := haa i
      rw [h] at this
      calc t = t * t * t⁻¹ := by group
        _ = 1 := by rw [this, mul_inv_cancel])
    exact (q8Facts_twin H (hMtw i)).exists_noncomm (a i) (haM i).1 h1 h2
  choose r hrM har using hr
  refine card_W_aux (M := M) (a := a) (r := r) (isPGroup_of_mem_WSet H.hW) (W_comm H) htW ht1
    (fun i => q8Facts_twin H (hMtw i)) (fun i => (haM i).1) (fun i => (haM i).2.1) haa hrM har
    (fun i j hij => twin_comm H (hMtw i) (hMtw j) (fun h => hij (hinj h)))
    (fun i => W_le_normalizer_twin H (hMtw i))
    (fun i => (twin_mem_DSet hP h2g H.hW htW (hMtw i).1 (hzM i)).2) fr.hy (sq_mem_W H fr)
    (exists_sq_tau H fr) ?_
  intro w hw hc
  apply hCP w hw
  intro p hp
  have hPle : ae6P Ω[R] t ≤ Subgroup.centralizer ({w} : Set Y) := by
    unfold ae6P
    refine iSup₂_le fun J hJ => ?_
    have hJt : J ∈ twinSet Ω[R] K := by rw [twinSet_eq_ae6Vc H]; exact hJ
    have hcJ : ∀ i, J = M i → J ≤ Subgroup.centralizer ({w} : Set Y) := by
      rintro i rfl x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hc i x hx).symm
    rcases twinSet_four hStd hF J hJt with h | h | h | h
    exacts [hcJ 0 h, hcJ 1 h, hcJ 2 h, hcJ 3 h]
  have h := hPle hp
  rw [Subgroup.mem_centralizer_singleton_iff] at h
  exact h.symm

theorem exists_W_of_dstarAdj (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) {J' : Subgroup Y}
    (hadj : dstarAdj Ω[R] K J') : ∃ W₁ ∈ WSet Ω[R], t ∈ W₁ ∧ J' ∈ DSet Ω[R] W₁ := by
  have hd := H.ex.1.datum
  have hΩ : HypOmegaGen Ω[R] := (CoreData.of_S H.ex.1.perp.core).hyp
  have h2g := H.ex.2.2.2.1
  obtain ⟨hJ'Ω, h' | h'⟩ := hadj
  · obtain ⟨W₁, hW₁, R₁, hR₁, T, hT, hR₁K, hTJ'⟩ :=
      CFSG.ClassicalInvolution.Q8P.Asc77.Thompson.exists_W_of_mem_omegaStarNbr hΩ hd.mem h'
    have htW₁ : t ∈ W₁ := (Q3CL.Thompson.uniqueInvolution_mem_W hΩ hW₁ hd.mem hR₁ hR₁K hd.hz).2
    have hTJ : T = J' := (hTJ'.2.2 J' le_rfl (h2g J' hJ'Ω) hTJ'.1).symm
    exact ⟨W₁, hW₁, htW₁, hTJ ▸ hT⟩
  · obtain ⟨W₁, hW₁, R₁, hR₁, T, hT, hR₁J', hTK⟩ :=
      CFSG.ClassicalInvolution.Q8P.Asc77.Thompson.exists_W_of_mem_omegaStarNbr hΩ hJ'Ω h'
    have htW₁ : t ∈ W₁ := (Q3CL.Thompson.uniqueInvolution_mem_W hΩ hW₁ hd.mem hT hTK hd.hz).2
    have hRJ : R₁ = J' := (hR₁J'.2.2 J' le_rfl (h2g J' hJ'Ω) hR₁J'.1).symm
    exact ⟨W₁, hW₁, htW₁, hRJ ▸ hR₁⟩

theorem member_le (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) {Hε : Subgroup Y}
    (hPH : ae6P Ω[R] t ≤ Hε) {J : Subgroup Y} (hJ : J ∈ Ω[R]) {g : Y} (hg : g ∈ Hε)
    (hz : IsUniqueInvolution J (g⁻¹ * t * g)) : J ≤ Hε := by
  have hinv := conjInvariant_conjClass (tightCore R)
  have h1 : IsUniqueInvolution (conjSub g J) t := by
    have := A6jB.isUniqueInvolution_conjSub hz g
    rwa [show g * (g⁻¹ * t * g) * g⁻¹ = t by group] at this
  have h2 : conjSub g J ≤ Hε := (le_ae6P (hinv g J hJ) h1).trans hPH
  calc J = conjSub g⁻¹ (conjSub g J) := (conjSub_inv_conjSub g J).symm
    _ ≤ conjSub g⁻¹ Hε := conjSub_mono h2
    _ = Hε := conjSub_eq_self_of_mem (Hε.inv_mem hg)

theorem tau_mem_P (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (fr : AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y) : y * t * y⁻¹ ∈ ae6P Ω[R] t := by
  have hd := H.ex.1.datum
  have hle : ∀ J ∈ twinSet Ω[R] K, J ≤ ae6P Ω[R] t := fun J hJ =>
    le_ae6P hJ.1 (isUniqueInvolution_of_mem_twinSet hd.hz hJ)
  rw [fr.hy]
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_) ?_
  · exact hle K (mem_twinSet_self hd.mem hd.hz) fr.h₁.1
  · exact hle K' hd.hK' fr.h₂.1
  · exact hle K₃ hd.hK₃ fr.h₃.1
  · exact hle K₄ H.ex.2.1.1 fr.h₄.1

theorem exists_N_conj_t (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) {s : Y} (hsW : s ∈ W) {g : Y}
    (hg : g * t * g⁻¹ = s) : ∃ m ∈ Subgroup.normalizer (W : Set Y), m * t * m⁻¹ = s := by
  have hStd := H.ex.1
  have hP := (CoreData.of_S hStd.perp.core).partIHypG
  have htW := t_mem_W H
  have htr : ∀ K₁ ∈ Ω[R], ∀ J ∈ Ω[R], ∃ x : Y, conjSub x K₁ = J := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact ⟨b * a⁻¹, by rw [conjSub_mul, conjSub_inv_conjSub]⟩
  have hnab : ¬ ∀ x y : ↥(muGroup Ω[R] W), x * y = y * x := fun hc =>
    TL4.not_comm_of_muIsoWylD4_gen (hStd.wyl W H.hW) fun x hx y hy =>
      congrArg Subtype.val (hc ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨S₀, hWS₀, hWC, -⟩ := A6Gen.exists_weaklyClosed_conj_of_nonab hP htr H.hW hnab
  have hWab : ∀ {v : Y}, v ∈ W → v ∈ Subgroup.centralizer (W : Set Y) := fun hv =>
    Subgroup.mem_centralizer_iff.mpr fun x hx =>
      Q3CL.Thompson.commutes_of_mem_WSet hP.hyp H.hW x hx _ hv
  obtain ⟨m, hmN, hm⟩ := Sec7.control_centralizer_of_weaklyClosed
    (S₀.isPGroup'.to_le hWS₀) hWC (hWab htW) (g := g) (by rw [hg]; exact hWab hsW)
  exact ⟨m, hmN, hm.trans hg⟩

theorem exists_M_conj_of_D (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) {J : Subgroup Y}
    (hJ : J ∈ Ω[R]) (hJD : J ∈ DSet Ω[R] W) : ∃ m ∈ MGrp Ω[R] W, conjSub m K = J := by
  have hStd := H.ex.1
  have hd := hStd.datum
  have hP := (CoreData.of_S hStd.perp.core).partIHypG
  have h2g : ∀ J ∈ Ω[R], IsPGroup 2 ↥J := H.ex.2.2.2.1
  have hK : K ∈ Ω[R] := hd.mem
  have c : Q3CL.Thompson.Ctx Ω[R] W := Q3CL.T8.ctxOf hP H.hW
  have hKsyl : IsSylow2In K K := ⟨le_rfl, h2g K hK, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
  obtain ⟨ρ, hρK⟩ : ∃ ρ : Asc77.Thompson.Rep Ω[R] W, ρ.K = K :=
    ⟨Q3CL.T8.mkRep hP H.hW hK H.hK hKsyl, rfl⟩
  have hJsyl : IsSylow2In J J := ⟨le_rfl, h2g J hJ, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
  obtain ⟨σ, hσK⟩ : ∃ σ : Asc77.Thompson.Rep Ω[R] W, σ.K = J :=
    ⟨Q3CL.T8.mkRep hP H.hW hJ hJD hJsyl, rfl⟩
  have hnc : ¬ DbarConnected Ω[R] W :=
    not_dbarConnected_of_wyl' hP hd (kPerp_datum hStd.perp hd.mem hd.hz) H.hW ρ hρK
      (hStd.wyl W H.hW)
  obtain ⟨m, hm, hmK⟩ := c.exists_conj_of_rep hP.cls hnc ρ σ
  exact ⟨m, hm, by rw [← hσK, ← hmK, hρK]⟩

theorem exists_M_conj_t (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) {s : Y} (hsW : s ∈ W) {g : Y}
    (hg : g * t * g⁻¹ = s) : ∃ m ∈ MGrp Ω[R] W, m * t * m⁻¹ = s := by
  have hd := H.ex.1.datum
  have hΩ : HypOmegaGen Ω[R] := (CoreData.of_S H.ex.1.perp.core).hyp
  have hQ8 := A6Gen.q8Omega_of_hyp H
  obtain ⟨m₀, hm₀N, hm₀⟩ := exists_N_conj_t H hsW hg
  have hJΩ : conjSub m₀ K ∈ Ω[R] := hΩ.conjInvariant m₀ K hd.mem
  have hJD : conjSub m₀ K ∈ DSet Ω[R] W := by
    have := hQ8.conjSub_mem_DSet H.hK m₀
    rwa [mem_normalizer_iff_conjSub_eq.mp hm₀N] at this
  obtain ⟨m, hm, hmK⟩ := exists_M_conj_of_D H hJΩ hJD
  refine ⟨m, hm, ?_⟩
  have h1 := A6jB.isUniqueInvolution_conjSub hd.hz m
  have h2 := A6jB.isUniqueInvolution_conjSub hd.hz m₀
  rw [hmK] at h1
  rw [hm₀] at h2
  exact h1.eq h2

theorem W_le (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) {Hε : Subgroup Y}
    (hPH : ae6P Ω[R] t ≤ Hε) (hMH : MGrp Ω[R] W ≤ Hε) : W ≤ Hε := by
  have hΩ : HypOmegaGen Ω[R] := (CoreData.of_S H.ex.1.perp.core).hyp
  have hQ8 := A6Gen.q8Omega_of_hyp H
  obtain ⟨η, ⟨S₀, hηS₀, -⟩, hWη⟩ := H.hW
  have hUW : ∀ U ∈ η, U ≤ W := fun U hU => hWη ▸ le_iSup₂_of_le U hU le_rfl
  rw [hWη]
  refine iSup₂_le fun U hU => ?_
  have hU' : U ∈ USet Ω[R] := (hηS₀.1 hU).1
  obtain ⟨R₁, -, J₁, hJ₁, hRJ₁, hUR, hcyc, -, -⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hU'
  have hUJ₁ : U ≤ J₁ := hUR.trans hRJ₁.1
  have h4 : Nat.card U = 4 := hQ8.natCard_of_mem_USet hU'
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hgo : orderOf (g : Y) = 4 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, h4]
  obtain ⟨z₁, hz₁⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ₁
  have huu : (g : Y) * g = z₁ := Asc77.sq_eq_of_orderOf_four hz₁ (hUJ₁ g.2) hgo
  have hz₁W : z₁ ∈ W := huu ▸ W.mul_mem (hUW U hU g.2) (hUW U hU g.2)
  obtain ⟨g₁, hg₁, -⟩ := exists_conj_t H hJ₁ hz₁
  obtain ⟨m, hm, hmt⟩ := exists_M_conj_t H hz₁W hg₁
  have hz : IsUniqueInvolution J₁ (m⁻¹⁻¹ * t * m⁻¹) := by rwa [inv_inv, hmt]
  exact hUJ₁.trans (member_le H hPH hJ₁ (Hε.inv_mem (hMH hm)) hz)

theorem exists_transpP (hQ8 : AE6ModelQ8) (hSmall : AE6ModelSmall)
    (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) {Hε : Subgroup Y} (hPH : ae6P Ω[R] t ≤ Hε)
    (e₀ : ↥Hε ≃* AE6Om) : ∃ e : ↥Hε ≃* AE6Om, AE6TranspP e t (twinSet Ω[R] K) (ae6P Ω[R] t) := by
  have hd := H.ex.1.datum
  have hinv := conjInvariant_conjClass (tightCore R)
  have hVt : ∀ J ∈ twinSet Ω[R] K, IsUniqueInvolution J t := fun J hJ =>
    isUniqueInvolution_of_mem_twinSet hd.hz hJ
  have hVH : ∀ J ∈ twinSet Ω[R] K, J ≤ Hε := fun J hJ => (le_ae6P hJ.1 (hVt J hJ)).trans hPH
  have hKV : K ∈ twinSet Ω[R] K := mem_twinSet_self hd.mem hd.hz
  have htH : t ∈ Hε := hVH K hKV hd.hz.mem
  have hsm : ∀ (e : ↥Hε ≃* AE6Om) (J : Subgroup Y), J ∈ twinSet Ω[R] K →
      AE6SmallQ8 (e ⟨t, htH⟩) (J.comap (ae6Emb e)) := by
    intro e J hJ
    have h1 := A6jB.smallQ8_map e (A6jB.smallQ8_of_member H hJ.1 (hVt J hJ) (hVH J hJ))
    have h2 : (J.subgroupOf Hε).map e.toMonoidHom = J.comap (ae6Emb e) := by
      ext x
      rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_comap, ae6Emb_apply]
    rw [h2] at h1
    exact h1
  obtain ⟨g, hg⟩ := hQ8 _ _ _ _ (hsm e₀ K hKV) hSmall.1
  set e₁ := e₀.trans (MulAut.conj g) with he₁
  have hz₁ : ae6Emb e₁ ae6ModelZ = t := by
    rw [he₁, ae6Emb_trans_conj]
    have h1 : g⁻¹ * ae6ModelZ * g = e₀ ⟨t, htH⟩ := by rw [← hg]; group
    rw [h1, ae6Emb_e]
  have he₁t : e₁ ⟨t, htH⟩ = ae6ModelZ := by
    apply e₁.symm.injective
    rw [MulEquiv.symm_apply_apply]
    apply Subtype.ext
    rw [← ae6Emb_apply, hz₁]
  have hfr := ae6Emb_range e₁
  have hfwd : ∀ J ∈ twinSet Ω[R] K,
      J.comap (ae6Emb e₁) ∈ ae6ModelTwins ∧ (J.comap (ae6Emb e₁)).map (ae6Emb e₁) = J := by
    intro J hJ
    refine ⟨hSmall.2 _ ?_, Subgroup.map_comap_eq_self (by rw [hfr]; exact hVH J hJ)⟩
    have h1 := hsm e₁ J hJ
    rwa [he₁t] at h1
  have htwins : ∀ J, J ∈ twinSet Ω[R] K ↔ ∃ J₀ ∈ ae6ModelTwins, J₀.map (ae6Emb e₁) = J := by
    intro J
    constructor
    · intro hJ
      exact ⟨_, (hfwd J hJ).1, (hfwd J hJ).2⟩
    · rintro ⟨J₀, ⟨c, hc, rfl⟩, rfl⟩
      obtain ⟨⟨c₁, hc₁, hK₁⟩, hKmap⟩ := hfwd K hKV
      have e1 : conjSub c ae6ModelK = conjSub (c * c₁⁻¹) (K.comap (ae6Emb e₁)) := by
        rw [← hK₁, ← conjSub_mul, inv_mul_cancel_right]
      rw [e1, map_conjSub_hom, hKmap]
      have hcc : c * c₁⁻¹ ∈ Subgroup.centralizer ({ae6ModelZ} : Set AE6Om) :=
        Subgroup.mul_mem _ hc (Subgroup.inv_mem _ hc₁)
      have hgt : ae6Emb e₁ (c * c₁⁻¹) * t * (ae6Emb e₁ (c * c₁⁻¹))⁻¹ = t := by
        rw [← hz₁, ← map_inv, ← map_mul, ← map_mul]
        rw [Subgroup.mem_centralizer_singleton_iff] at hcc
        rw [hcc, mul_inv_cancel_right]
      refine ⟨hinv _ K hd.mem, t, hd.hz, ?_⟩
      have h1 := A6jB.isUniqueInvolution_conjSub hd.hz (ae6Emb e₁ (c * c₁⁻¹))
      rwa [hgt] at h1
  have hPeq : ae6ModelP.map (ae6Emb e₁) = ae6P Ω[R] t := by
    unfold ae6ModelP ae6P
    rw [sSup_eq_iSup]
    simp only [Subgroup.map_iSup]
    apply le_antisymm
    · refine iSup₂_le fun J₀ hJ₀ => ?_
      have hJ := (htwins (J₀.map (ae6Emb e₁))).2 ⟨J₀, hJ₀, rfl⟩
      rw [twinSet_eq_ae6Vc H] at hJ
      exact le_iSup₂_of_le (J₀.map (ae6Emb e₁)) hJ le_rfl
    · refine iSup₂_le fun J hJ => ?_
      have hJ' : J ∈ twinSet Ω[R] K := by rw [twinSet_eq_ae6Vc H]; exact hJ
      obtain ⟨J₀, hJ₀, rfl⟩ := (htwins J).1 hJ'
      exact le_iSup₂_of_le J₀ hJ₀ le_rfl
  exact ⟨e₁, hz₁, htwins, hPeq⟩

theorem exists_transp (hQ8 : AE6ModelQ8) (hSmall : AE6ModelSmall) (hFW : AE6ModelFW)
    (hC2 : AE6ModelC2) (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (fr : AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y) {Hε : Subgroup Y} (hPH : ae6P Ω[R] t ≤ Hε)
    (hWH : W ≤ Hε) (e₀ : ↥Hε ≃* AE6Om) :
    ∃ e : ↥Hε ≃* AE6Om, AE6TranspP e t (twinSet Ω[R] K) (ae6P Ω[R] t) ∧
      ae6ModelW.map (ae6Emb e) = W := by
  have hd := H.ex.1.datum
  have hP := (CoreData.of_S H.ex.1.perp.core).partIHypG
  have h2g := H.ex.2.2.2.1
  have htW := t_mem_W H
  obtain ⟨e₁, hT₁⟩ := exists_transpP hQ8 hSmall H hPH e₀
  have hfi := ae6Emb_injective e₁
  have hfr := ae6Emb_range e₁
  have h64 := card_W H fr fun w hw hc => cent_P_transp hSmall hC2 hT₁ (hWH hw) hc
  have hW₁map : (W.comap (ae6Emb e₁)).map (ae6Emb e₁) = W :=
    Subgroup.map_comap_eq_self (by rw [hfr]; exact hWH)
  have hadm : AE6Admissible (W.comap (ae6Emb e₁)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx y hy
      apply hfi
      rw [map_mul, map_mul]
      exact W_comm H _ hx _ hy
    · calc Nat.card ↥(W.comap (ae6Emb e₁))
          = Nat.card ↥((W.comap (ae6Emb e₁)).map (ae6Emb e₁)) :=
            (Subgroup.card_map_of_injective hfi).symm
        _ = 64 := by rw [hW₁map, h64]
    · intro J₀ hJ₀
      have hJ := (hT₁.twins_iff (J₀.map (ae6Emb e₁))).2 ⟨J₀, hJ₀, rfl⟩
      have hJN : J₀.map (ae6Emb e₁) ≤ Subgroup.normalizer (W : Set Y) :=
        (twin_mem_DSet hP h2g H.hW htW hJ.1 (isUniqueInvolution_of_mem_twinSet hd.hz hJ)).2
      refine ⟨?_, ?_⟩
      · intro x hx
        have hxN := hJN (Subgroup.mem_map_of_mem _ hx)
        rw [Subgroup.mem_normalizer_iff]
        intro h
        rw [Subgroup.mem_comap, Subgroup.mem_comap, map_mul, map_mul, map_inv]
        exact Subgroup.mem_normalizer_iff.mp hxN _
      · have e1 : (J₀ ⊓ W.comap (ae6Emb e₁)).map (ae6Emb e₁) = J₀.map (ae6Emb e₁) ⊓ W := by
          rw [Subgroup.map_inf_eq _ _ _ hfi, hW₁map]
        calc Nat.card ↥(J₀ ⊓ W.comap (ae6Emb e₁))
            = Nat.card ↥((J₀ ⊓ W.comap (ae6Emb e₁)).map (ae6Emb e₁)) :=
              (Subgroup.card_map_of_injective hfi).symm
          _ = 4 := by rw [e1]; exact card_twin_inf_W H hJ
  obtain ⟨c, hc, hcW⟩ := hFW.2 _ hadm
  obtain ⟨hT, hB⟩ := hT₁.move hc
  exact ⟨_, hT, by rw [hB, hcW, hW₁map]⟩

theorem stepF (hF : AE6ModelF) (hW1 : V3AE6NoWt1 n) (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (fr : AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y) {Hε : Subgroup Y} {e : ↥Hε ≃* AE6Om}
    (hT : AE6TranspP e t (twinSet Ω[R] K) (ae6P Ω[R] t)) (hTW : ae6ModelW.map (ae6Emb e) = W)
    {c : Y} (hc : c ∈ Subgroup.centralizer ({t} : Set Y)) :
    ∃ h, h ∈ Hε ∧ h ∈ Subgroup.centralizer ({t} : Set Y) ∧ ∀ w ∈ W, ∃ w' ∈ W,
      ∀ p ∈ ae6P Ω[R] t, (c * w * c⁻¹) * p * (c * w * c⁻¹)⁻¹ =
        (h * w' * h⁻¹) * p * (h * w' * h⁻¹)⁻¹ := by
  classical
  have hd := H.ex.1.datum
  have hinv := conjInvariant_conjClass (tightCore R)
  have hfi : Function.Injective (ae6Emb e) := ae6Emb_injective e
  have hN : Subgroup.centralizer ({t} : Set Y) ≤ Subgroup.normalizer (ae6P Ω[R] t : Set Y) :=
    fun c hc => mem_normalizer_ae6P hinv hc
  set ρ := ae6Rho e hT.P_eq hN with hρdef
  have hρ : ∀ (c : ↥(Subgroup.centralizer ({t} : Set Y))) (p : ↥ae6ModelP),
      ae6Emb e ((ρ c p : ↥ae6ModelP) : AE6Om) = (c : Y) * ae6Emb e p * (c : Y)⁻¹ :=
    ae6Rho_apply e hT.P_eq hN
  have hPimg : ∀ q ∈ ae6P Ω[R] t, ∃ p : ↥ae6ModelP, ae6Emb e p = q := by
    intro q hq
    rw [← hT.P_eq] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    exact ⟨⟨p, hp⟩, rfl⟩
  have hfz : ∀ x : AE6Om, x ∈ Subgroup.centralizer ({ae6ModelZ} : Set AE6Om) →
      ae6Emb e x ∈ Subgroup.centralizer ({t} : Set Y) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    rw [← hT.z_eq, ← map_mul, ← map_mul, hx]
  have hconjV : ∀ c ∈ Subgroup.centralizer ({t} : Set Y), ∀ J ∈ twinSet Ω[R] K,
      conjSub c J ∈ twinSet Ω[R] K := by
    intro c hc J hJ
    have hct : c * t * c⁻¹ = t := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hc
      rw [hc, mul_inv_cancel_right]
    refine ⟨hinv c J hJ.1, t, hd.hz, ?_⟩
    have h1 := A6jB.isUniqueInvolution_conjSub (isUniqueInvolution_of_mem_twinSet hd.hz hJ) c
    rwa [hct] at h1
  have hJP : ∀ J₀ ∈ ae6ModelTwins, J₀ ≤ ae6ModelP := fun J₀ hJ₀ => le_sSup hJ₀
  have hX1 : ae6ConjAut (Subgroup.centralizer ({ae6ModelZ} : Set AE6Om)) ⊆ (ρ.range : Set _) := by
    rintro α ⟨c₀, hc₀, hα⟩
    refine ⟨⟨ae6Emb e c₀, hfz c₀ hc₀⟩, MulEquiv.ext fun p => Subtype.ext ?_⟩
    apply hfi
    rw [hρ, hα p, map_mul, map_mul, map_inv]
  have hX2 : ∀ x ∈ ρ.range, ∀ J ∈ ae6ModelTwins, ∃ J' ∈ ae6ModelTwins,
      ∀ p : ↥ae6ModelP, (p : AE6Om) ∈ J ↔ (x p : AE6Om) ∈ J' := by
    rintro _ ⟨c, rfl⟩ J hJ
    have hJV := (hT.twins_iff (J.map (ae6Emb e))).2 ⟨J, hJ, rfl⟩
    obtain ⟨J', hJ', hJ'eq⟩ := (hT.twins_iff _).1 (hconjV c c.2 _ hJV)
    refine ⟨J', hJ', fun p => ?_⟩
    rw [← Subgroup.mem_map_iff_mem hfi (K := J'), hJ'eq, hρ, mem_conjSub_iff,
      show (c : Y)⁻¹ * ((c : Y) * ae6Emb e p * (c : Y)⁻¹) * c = ae6Emb e p by group,
      Subgroup.mem_map_iff_mem hfi]
  have hX3 : ∀ x ∈ ρ.range, orderOf x = 3 →
      (∀ J ∈ ae6ModelTwins, ∀ p : ↥ae6ModelP, (p : AE6Om) ∈ J ↔ (x p : AE6Om) ∈ J) →
      Set.ncard {J | J ∈ ae6ModelTwins ∧ ∃ p : ↥ae6ModelP, (p : AE6Om) ∈ J ∧ x p ≠ p} ≠ 1 := by
    rintro _ ⟨c, rfl⟩ h3 hnormJ
    have hc3 : ∀ J ∈ twinSet Ω[R] K, (c : Y) ^ 3 ∈ Subgroup.centralizer (J : Set Y) := by
      intro J hJ
      rw [mem_centralizer_iff_conj]
      intro q hq
      have hqP : q ∈ ae6P Ω[R] t := le_ae6P hJ.1 (isUniqueInvolution_of_mem_twinSet hd.hz hJ) hq
      obtain ⟨p, rfl⟩ := hPimg q hqP
      have h1 : ρ (c ^ 3) = 1 := by rw [map_pow, ← h3, pow_orderOf_eq_one]
      have h2 := hρ (c ^ 3) p
      rw [h1, MulAut.one_apply] at h2
      simpa using h2.symm
    have hcV : ∀ J ∈ twinSet Ω[R] K, ∀ q ∈ J, (c : Y) * q * (c : Y)⁻¹ ∈ J := by
      intro J hJ q hq
      obtain ⟨J₀, hJ₀, rfl⟩ := (hT.twins_iff J).1 hJ
      obtain ⟨p, hp, rfl⟩ := hq
      have hpP : p ∈ ae6ModelP := hJP J₀ hJ₀ hp
      rw [show ae6Emb e p = ae6Emb e ((⟨p, hpP⟩ : ↥ae6ModelP) : AE6Om) from rfl, ← hρ c ⟨p, hpP⟩]
      exact Subgroup.mem_map_of_mem _ ((hnormJ J₀ hJ₀ ⟨p, hpP⟩).mp hp)
    have hcN : ∀ J ∈ twinSet Ω[R] K, (c : Y) ∈ Subgroup.normalizer (J : Set Y) := by
      intro J hJ
      refine mem_normalizer_of_conjSub_le fun q hq => ?_
      rw [mem_conjSub_iff] at hq
      have h1 := hcV J hJ _ hq
      rwa [show (c : Y) * ((c : Y)⁻¹ * q * c) * (c : Y)⁻¹ = q by group] at h1
    have hN0 : orderOf (c : Y) ≠ 0 := (orderOf_pos (c : Y)).ne'
    set m := orderOf (c : Y) / 3 ^ (orderOf (c : Y)).factorization 3 with hmdef
    have hm : Nat.Coprime 3 m := Nat.coprime_ordCompl Nat.prime_three hN0
    have hm0 : m ≠ 0 := by
      intro h0
      rw [h0] at hm
      norm_num at hm
    have hc₃C : (c : Y) ^ m ∈ Subgroup.centralizer ({t} : Set Y) := Subgroup.pow_mem _ c.2 m
    have hc₃3 : IsPGroup 3 (Subgroup.zpowers ((c : Y) ^ m)) := by
      apply IsPGroup.of_card (n := (orderOf (c : Y)).factorization 3)
      rw [Nat.card_zpowers, orderOf_pow' _ hm0]
      have hdvd : m ∣ orderOf (c : Y) := Nat.div_dvd_of_dvd (Nat.ordProj_dvd _ 3)
      rw [Nat.gcd_eq_right hdvd]
      exact Nat.div_eq_of_eq_mul_left (Nat.pos_of_ne_zero hm0)
        (Nat.ordProj_mul_ordCompl_eq_self _ 3).symm
    have hc₃N : ∀ J ∈ twinSet Ω[R] K, (c : Y) ^ m ∈ Subgroup.normalizer (J : Set Y) :=
      fun J hJ => Subgroup.pow_mem _ (hcN J hJ) m
    have hne := hW1 Y R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y H fr _ hc₃C hc₃3 hc₃N
    have hiff : ∀ J ∈ twinSet Ω[R] K, (∃ q ∈ J, (c : Y) ^ m * q * ((c : Y) ^ m)⁻¹ ≠ q) ↔
        (∃ q ∈ J, (c : Y) * q * (c : Y)⁻¹ ≠ q) := by
      intro J hJ
      have hA : (c : Y) ∈ Subgroup.centralizer (J : Set Y) ↔
          (c : Y) ^ m ∈ Subgroup.centralizer (J : Set Y) :=
        ⟨fun h => Subgroup.pow_mem _ h m, fun h => mem_centralizer_of_pow hm (hc3 J hJ) h⟩
      rw [mem_centralizer_iff_conj, mem_centralizer_iff_conj] at hA
      constructor
      · rintro ⟨q, hq, hqne⟩
        by_contra hall
        exact hqne (hA.mp (fun q' hq' => by_contra fun hne => hall ⟨q', hq', hne⟩) q hq)
      · rintro ⟨q, hq, hqne⟩
        by_contra hall
        exact hqne (hA.mpr (fun q' hq' => by_contra fun hne => hall ⟨q', hq', hne⟩) q hq)
    have hset : (fun J₀ : Subgroup AE6Om => J₀.map (ae6Emb e)) ''
        {J | J ∈ ae6ModelTwins ∧ ∃ p : ↥ae6ModelP, (p : AE6Om) ∈ J ∧ ρ c p ≠ p} =
        {J | J ∈ twinSet Ω[R] K ∧ ∃ q ∈ J, (c : Y) ^ m * q * ((c : Y) ^ m)⁻¹ ≠ q} := by
      ext J
      constructor
      · rintro ⟨J₀, ⟨hJ₀, p, hpJ, hpne⟩, rfl⟩
        have hJV := (hT.twins_iff _).2 ⟨J₀, hJ₀, rfl⟩
        refine ⟨hJV, (hiff _ hJV).2 ⟨ae6Emb e p, Subgroup.mem_map_of_mem _ hpJ, ?_⟩⟩
        rw [← hρ]
        intro h
        exact hpne (Subtype.ext (hfi h))
      · rintro ⟨hJV, hex⟩
        obtain ⟨J₀, hJ₀, rfl⟩ := (hT.twins_iff J).1 hJV
        obtain ⟨q, hq, hqne⟩ := (hiff _ hJV).1 hex
        obtain ⟨p, hp, rfl⟩ := hq
        have hpP : p ∈ ae6ModelP := hJP J₀ hJ₀ hp
        refine ⟨J₀, ⟨hJ₀, ⟨p, hpP⟩, hp, ?_⟩, rfl⟩
        intro h
        apply hqne
        have h1 := hρ c ⟨p, hpP⟩
        rw [h] at h1
        exact h1.symm
    rw [← Set.ncard_image_of_injective _ (Subgroup.map_injective hfi), hset]
    exact hne
  obtain ⟨β, ⟨c₀, hc₀, hβ⟩, himg⟩ := hF ρ.range hX1 hX2 hX3 (ρ ⟨c, hc⟩) ⟨⟨c, hc⟩, rfl⟩
  refine ⟨ae6Emb e c₀, ae6Emb_mem e c₀, hfz c₀ hc₀, fun w hw => ?_⟩
  have hwC : w ∈ Subgroup.centralizer ({t} : Set Y) := W_le_cent H hw
  obtain ⟨w₀, hw₀, rfl⟩ : ∃ w₀ ∈ ae6ModelW, ae6Emb e w₀ = w := by
    rw [← hTW] at hw
    exact hw
  have hρw : ρ ⟨ae6Emb e w₀, hwC⟩ ∈ ae6ConjAut ae6ModelW :=
    ⟨w₀, hw₀, fun p => hfi (by rw [hρ, map_mul, map_mul, map_inv])⟩
  have hmem : ρ ⟨c, hc⟩ * ρ ⟨ae6Emb e w₀, hwC⟩ * (ρ ⟨c, hc⟩)⁻¹ ∈
      (fun α => β * α * β⁻¹) '' ae6ConjAut ae6ModelW := by
    rw [← himg]
    exact ⟨_, hρw, rfl⟩
  obtain ⟨α', ⟨w₀', hw₀', hα'⟩, hαeq⟩ := hmem
  have hw' : ae6Emb e w₀' ∈ W := by
    rw [← hTW]
    exact Subgroup.mem_map_of_mem _ hw₀'
  refine ⟨ae6Emb e w₀', hw', fun q hq => ?_⟩
  obtain ⟨p, rfl⟩ := hPimg q hq
  have hβinv : ∀ r : ↥ae6ModelP, ((β⁻¹ r : ↥ae6ModelP) : AE6Om) = c₀⁻¹ * r * c₀ := by
    intro r
    have h1 : β (β⁻¹ r) = r := by rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
    have h2 := hβ (β⁻¹ r)
    rw [h1] at h2
    rw [h2]
    group
  have hR : ae6Emb e (((ρ ⟨c, hc⟩ * ρ ⟨ae6Emb e w₀, hwC⟩ * (ρ ⟨c, hc⟩)⁻¹) p : ↥ae6ModelP) :
      AE6Om) = (c * ae6Emb e w₀ * c⁻¹) * ae6Emb e p * (c * ae6Emb e w₀ * c⁻¹)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, hρ]
    rfl
  have hL : ae6Emb e (((β * α' * β⁻¹) p : ↥ae6ModelP) : AE6Om) =
      (ae6Emb e c₀ * ae6Emb e w₀' * (ae6Emb e c₀)⁻¹) * ae6Emb e p *
        (ae6Emb e c₀ * ae6Emb e w₀' * (ae6Emb e c₀)⁻¹)⁻¹ := by
    rw [MulAut.mul_apply, MulAut.mul_apply, hβ, hα', hβinv]
    simp only [map_mul, map_inv]
    group
  rw [← hR, ← hαeq, hL]

theorem step2 (hSmall : AE6ModelSmall) (hC3 : AE6ModelC3) (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (fr : AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y) {Hε : Subgroup Y} {e : ↥Hε ≃* AE6Om}
    (hT : AE6TranspP e t (twinSet Ω[R] K) (ae6P Ω[R] t)) (hTW : ae6ModelW.map (ae6Emb e) = W)
    (hPH : ae6P Ω[R] t ≤ Hε) (hWH : W ≤ Hε)
    (hCW : ∀ w ∈ W, (∀ p ∈ ae6P Ω[R] t, w * p = p * w) → w = 1 ∨ w = t)
    {d : Y} (hdC : d ∈ Subgroup.centralizer ({t} : Set Y))
    (hdW : ∀ w ∈ W, ∃ w' ∈ W, ∃ z : Y, (∀ g ∈ Hε, z * g = g * z) ∧ d * w * d⁻¹ = w' * z) :
    conjSub d W = W := by
  classical
  have hd := H.ex.1.datum
  have hΩ : HypOmegaGen Ω[R] := (CoreData.of_S H.ex.1.perp.core).hyp
  have hinv := conjInvariant_conjClass (tightCore R)
  have hQ8 := A6Gen.q8Omega_of_hyp H
  have hfi := ae6Emb_injective e
  have hZ : ∀ z ∈ Hε, (∀ g ∈ Hε, z * g = g * z) → z = 1 := fun z hz hc =>
    center_eq_one hSmall e hz hc
  have htP : t ∈ ae6P Ω[R] t := le_ae6P hd.mem hd.hz hd.hz.mem
  have htH : t ∈ Hε := hPH htP
  have hdN : d ∈ Subgroup.normalizer (ae6P Ω[R] t : Set Y) := mem_normalizer_ae6P hinv hdC
  have hdP : ∀ q ∈ ae6P Ω[R] t, d * q * d⁻¹ ∈ ae6P Ω[R] t := fun q hq =>
    (Subgroup.mem_normalizer_iff.mp hdN q).mp hq
  have hdt : d * t * d⁻¹ = t := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hdC
    rw [hdC, mul_inv_cancel_right]
  have ha : ∀ w ∈ W, (∀ g ∈ Hε, d * w * d⁻¹ * g = g * (d * w * d⁻¹)) → d * w * d⁻¹ = 1 := by
    intro w hw hc
    have hwP : ∀ p ∈ ae6P Ω[R] t, w * p = p * w := by
      intro p hp
      have h1 := hc _ (hPH (hdP p hp))
      have h2 : d * (w * p) * d⁻¹ = d * (p * w) * d⁻¹ := by
        calc d * (w * p) * d⁻¹ = (d * w * d⁻¹) * (d * p * d⁻¹) := by group
          _ = (d * p * d⁻¹) * (d * w * d⁻¹) := h1
          _ = d * (p * w) * d⁻¹ := by group
      exact mul_left_cancel (mul_right_cancel h2)
    rcases hCW w hw hwP with h | h
    · rw [h]
      group
    · exfalso
      apply hd.hz.ne_one
      apply hZ t htH
      intro g hg
      have h1 := hc g hg
      rw [h, hdt] at h1
      exact h1
  have hb : ∀ w ∈ W, d * w * d⁻¹ ∈ ae6P Ω[R] t → d * w * d⁻¹ ∈ W := by
    intro w hw hP
    obtain ⟨w', hw', z, hz, he⟩ := hdW w hw
    have hzH : z ∈ Hε := by
      have h1 : z = w'⁻¹ * (d * w * d⁻¹) := by rw [he]; group
      rw [h1]
      exact Hε.mul_mem (Hε.inv_mem (hWH hw')) (hPH hP)
    rw [he, hZ z hzH hz, mul_one]
    exact hw'
  have hc : ∀ v ∈ W, v ∈ ae6P Ω[R] t → ∃ w ∈ W, d * w * d⁻¹ = v := by
    intro v hv hvP
    have hle : conjSub d (W ⊓ ae6P Ω[R] t) ≤ W ⊓ ae6P Ω[R] t := by
      intro x hx
      rw [mem_conjSub_iff] at hx
      have hx1 : d * (d⁻¹ * x * d) * d⁻¹ = x := by group
      have hxP : x ∈ ae6P Ω[R] t := by
        rw [← hx1]
        exact hdP _ hx.2
      refine ⟨?_, hxP⟩
      rw [← hx1]
      exact hb _ hx.1 (by rw [hx1]; exact hxP)
    have heq : conjSub d (W ⊓ ae6P Ω[R] t) = W ⊓ ae6P Ω[R] t :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [natCard_conjSub])
    have hv' : v ∈ conjSub d (W ⊓ ae6P Ω[R] t) := by
      rw [heq]
      exact ⟨hv, hvP⟩
    rw [mem_conjSub_iff] at hv'
    exact ⟨_, hv'.1, by group⟩
  obtain ⟨η, ⟨S₀, hηS₀, -⟩, hWη⟩ := H.hW
  have hUW : ∀ U ∈ η, U ≤ W := fun U hU => hWη ▸ le_iSup₂_of_le U hU le_rfl
  have hgen : ∀ U ∈ η, conjSub d U ≤ W := by
    intro U hU
    have hU' : U ∈ USet Ω[R] := (hηS₀.1 hU).1
    obtain ⟨R₁, -, J₁, hJ₁, hRJ₁, hUR, hcyc, -, -⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hU'
    have hUJ₁ : U ≤ J₁ := hUR.trans hRJ₁.1
    have h4 : Nat.card U = 4 := hQ8.natCard_of_mem_USet hU'
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    have hgo : orderOf (g : Y) = 4 := by
      rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, h4]
    obtain ⟨z₁, hz₁⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ₁
    have huu : (g : Y) * g = z₁ := Asc77.sq_eq_of_orderOf_four hz₁ (hUJ₁ g.2) hgo
    have huW : (g : Y) ∈ W := hUW U hU g.2
    suffices hu' : d * g * d⁻¹ ∈ W by
      intro x hx
      rw [mem_conjSub_iff] at hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨d⁻¹ * x * d, hx⟩)
      have hk' : (g : Y) ^ k = d⁻¹ * x * d := congrArg Subtype.val hk
      have hx' : x = (MulAut.conj d) ((g : Y) ^ k) := by
        rw [hk', MulAut.conj_apply]
        group
      rw [hx', map_zpow, MulAut.conj_apply]
      exact Subgroup.zpow_mem _ hu' k
    by_cases hu'P : d * g * d⁻¹ ∈ ae6P Ω[R] t
    · exact hb _ huW hu'P
    obtain ⟨w₁, hw₁, z, hz, he⟩ := hdW _ huW
    have hz1_of : d * g * d⁻¹ ∈ Hε → z = 1 := by
      intro h
      apply hZ z _ hz
      have h1 : z = w₁⁻¹ * (d * g * d⁻¹) := by rw [he]; group
      rw [h1]
      exact Hε.mul_mem (Hε.inv_mem (hWH hw₁)) h
    have hw₁P : w₁ ∉ ae6P Ω[R] t := by
      intro hw₁P
      obtain ⟨w₂, hw₂, hw₂e⟩ := hc w₁ hw₁ hw₁P
      have hzd : z = d * (w₂⁻¹ * g) * d⁻¹ := by
        calc z = w₁⁻¹ * (d * g * d⁻¹) := by rw [he]; group
          _ = d * (w₂⁻¹ * g) * d⁻¹ := by rw [← hw₂e]; group
      have hz1 : z = 1 := by
        rw [hzd]
        apply ha _ (W.mul_mem (W.inv_mem hw₂) huW)
        rw [← hzd]
        exact hz
      apply hu'P
      rw [he, hz1, mul_one]
      exact hw₁P
    have hz₁W : z₁ ∈ W := huu ▸ W.mul_mem huW huW
    obtain ⟨g₁, hg₁, -⟩ := exists_conj_t H hJ₁ hz₁
    have hz₁P : z₁ ∈ ae6P Ω[R] t := by
      rcases A6Wt.mem_tG_W H fr hz₁W hg₁ with h | h | h
      · rw [h]; exact htP
      · rw [h]; exact tau_mem_P H fr
      · rw [h]; exact (ae6P Ω[R] t).mul_mem htP (tau_mem_P H fr)
    have hu'2 : (d * g * d⁻¹) * (d * g * d⁻¹) = d * z₁ * d⁻¹ := by rw [← huu]; group
    have hu'2P : (d * g * d⁻¹) * (d * g * d⁻¹) ∈ ae6P Ω[R] t := by
      rw [hu'2]
      exact hdP _ hz₁P
    have hzw : z * w₁ = w₁ * z := hz w₁ (hWH hw₁)
    have hzz : z * z = 1 := by
      have hzzH : z * z ∈ Hε := by
        have h1 : z * z = (w₁ * w₁)⁻¹ * ((d * g * d⁻¹) * (d * g * d⁻¹)) := by
          rw [he]
          calc z * z = (w₁ * w₁)⁻¹ * (w₁ * (w₁ * z) * z) := by group
            _ = (w₁ * w₁)⁻¹ * (w₁ * (z * w₁) * z) := by rw [hzw]
            _ = (w₁ * w₁)⁻¹ * (w₁ * z * (w₁ * z)) := by group
        rw [h1]
        exact Hε.mul_mem (Hε.inv_mem (Hε.mul_mem (hWH hw₁) (hWH hw₁))) (hPH hu'2P)
      apply hZ _ hzzH
      intro g' hg'
      calc z * z * g' = z * (z * g') := by group
        _ = z * (g' * z) := by rw [hz g' hg']
        _ = (z * g') * z := by group
        _ = g' * z * z := by rw [hz g' hg']
        _ = g' * (z * z) := by group
    have hww : (d * g * d⁻¹) * (d * g * d⁻¹) = w₁ * w₁ := by
      rw [he]
      calc w₁ * z * (w₁ * z) = w₁ * (z * w₁) * z := by group
        _ = w₁ * w₁ * (z * z) := by rw [hzw]; group
        _ = w₁ * w₁ := by rw [hzz, mul_one]
    obtain ⟨w₀, hw₀, rfl⟩ : ∃ w₀ ∈ ae6ModelW, ae6Emb e w₀ = w₁ := by
      rw [← hTW] at hw₁
      exact hw₁
    have hw₀P : w₀ ∉ ae6ModelP := by
      intro h
      apply hw₁P
      rw [← hT.P_eq]
      exact Subgroup.mem_map_of_mem _ h
    obtain ⟨h₀, hh₀⟩ := hC3 w₀ hw₀ hw₀P
    have hsq : ae6Emb e w₀ * ae6Emb e w₀ = (ae6Emb e h₀)⁻¹ * t * ae6Emb e h₀ := by
      rw [← map_mul, ← sq, hh₀, map_mul, map_mul, map_inv, hT.z_eq]
    have hJ'z : IsUniqueInvolution (conjSub d J₁) ((ae6Emb e h₀)⁻¹ * t * ae6Emb e h₀) := by
      have h1 := A6jB.isUniqueInvolution_conjSub hz₁ d
      rwa [← hu'2, hww, hsq] at h1
    have hJ'H := member_le H hPH (hinv d J₁ hJ₁) (ae6Emb_mem e h₀) hJ'z
    have hu'H : d * g * d⁻¹ ∈ Hε := hJ'H (conj_mem_conjSub (hUJ₁ g.2))
    rw [he, hz1_of hu'H, mul_one]
    exact hw₁
  have hle : conjSub d W ≤ W := by
    calc conjSub d W = conjSub d (⨆ U ∈ η, U) := congrArg (conjSub d) hWη
      _ = ⨆ U ∈ η, conjSub d U := conjSub_iSup₂ d (fun U => U) η
      _ ≤ W := iSup₂_le fun U hU => hgen U hU
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [natCard_conjSub])

theorem conj_W_eq (hSmall : AE6ModelSmall) (hF : AE6ModelF) (hC1 : AE6ModelC1') (hC2 : AE6ModelC2)
    (hC3 : AE6ModelC3) (hW1 : V3AE6NoWt1 n) (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (fr : AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y) {Hε : Subgroup Y} {e : ↥Hε ≃* AE6Om}
    (hT : AE6TranspP e t (twinSet Ω[R] K) (ae6P Ω[R] t)) (hTW : ae6ModelW.map (ae6Emb e) = W)
    (hPH : ae6P Ω[R] t ≤ Hε) (hWH : W ≤ Hε) {c : Y} (hc : c ∈ Subgroup.centralizer ({t} : Set Y)) :
    ∃ h ∈ Hε, conjSub c W = conjSub h W := by
  have hinv := conjInvariant_conjClass (tightCore R)
  have hCW : ∀ w ∈ W, (∀ p ∈ ae6P Ω[R] t, w * p = p * w) → w = 1 ∨ w = t := fun w hw hcw =>
    cent_P_transp hSmall hC2 hT (hWH hw) hcw
  obtain ⟨h, hhH, hhC, hF'⟩ := stepF hF hW1 H fr hT hTW hc
  refine ⟨h, hhH, ?_⟩
  have hdC : h⁻¹ * c ∈ Subgroup.centralizer ({t} : Set Y) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hhC) hc
  have hdW : ∀ w ∈ W, ∃ w'' ∈ W, ∃ z : Y, (∀ g ∈ Hε, z * g = g * z) ∧
      (h⁻¹ * c) * w * (h⁻¹ * c)⁻¹ = w'' * z := by
    intro w hw
    obtain ⟨w', hw', hpw⟩ := hF' w hw
    have hx'P : ∀ p ∈ ae6P Ω[R] t,
        ((h * w' * h⁻¹)⁻¹ * (c * w * c⁻¹)) * p * ((h * w' * h⁻¹)⁻¹ * (c * w * c⁻¹))⁻¹ = p := by
      intro p hp
      calc ((h * w' * h⁻¹)⁻¹ * (c * w * c⁻¹)) * p * ((h * w' * h⁻¹)⁻¹ * (c * w * c⁻¹))⁻¹
          = (h * w' * h⁻¹)⁻¹ * ((c * w * c⁻¹) * p * (c * w * c⁻¹)⁻¹) * (h * w' * h⁻¹) := by group
        _ = (h * w' * h⁻¹)⁻¹ * ((h * w' * h⁻¹) * p * (h * w' * h⁻¹)⁻¹) * (h * w' * h⁻¹) := by
            rw [hpw p hp]
        _ = p := by group
    have hx''P : ∀ p ∈ ae6P Ω[R] t,
        (h⁻¹ * ((h * w' * h⁻¹)⁻¹ * (c * w * c⁻¹)) * h) * p =
          p * (h⁻¹ * ((h * w' * h⁻¹)⁻¹ * (c * w * c⁻¹)) * h) := by
      intro p hp
      have hhp : h * p * h⁻¹ ∈ ae6P Ω[R] t :=
        (Subgroup.mem_normalizer_iff.mp (mem_normalizer_ae6P hinv hhC) p).mp hp
      have h2 := hx'P _ hhp
      have h3 : (h⁻¹ * ((h * w' * h⁻¹)⁻¹ * (c * w * c⁻¹)) * h) * p *
          (h⁻¹ * ((h * w' * h⁻¹)⁻¹ * (c * w * c⁻¹)) * h)⁻¹ = p := by
        calc (h⁻¹ * ((h * w' * h⁻¹)⁻¹ * (c * w * c⁻¹)) * h) * p *
              (h⁻¹ * ((h * w' * h⁻¹)⁻¹ * (c * w * c⁻¹)) * h)⁻¹
            = h⁻¹ * (((h * w' * h⁻¹)⁻¹ * (c * w * c⁻¹)) * (h * p * h⁻¹) *
                ((h * w' * h⁻¹)⁻¹ * (c * w * c⁻¹))⁻¹) * h := by group
          _ = p := by rw [h2]; group
      calc (h⁻¹ * ((h * w' * h⁻¹)⁻¹ * (c * w * c⁻¹)) * h) * p
          = ((h⁻¹ * ((h * w' * h⁻¹)⁻¹ * (c * w * c⁻¹)) * h) * p *
              (h⁻¹ * ((h * w' * h⁻¹)⁻¹ * (c * w * c⁻¹)) * h)⁻¹) *
              (h⁻¹ * ((h * w' * h⁻¹)⁻¹ * (c * w * c⁻¹)) * h) := by group
        _ = p * (h⁻¹ * ((h * w' * h⁻¹)⁻¹ * (c * w * c⁻¹)) * h) := by rw [h3]
    obtain ⟨ε₀, hε₀, hε₀g⟩ := step1 hC1 hC2 hinv hT hx''P
    have hε₀W : ε₀ ∈ W := by
      rcases hε₀ with rfl | rfl
      · exact W.one_mem
      · exact t_mem_W H
    refine ⟨w' * ε₀, W.mul_mem hw' hε₀W,
      ε₀⁻¹ * (h⁻¹ * ((h * w' * h⁻¹)⁻¹ * (c * w * c⁻¹)) * h), ?_, ?_⟩
    · intro g hg
      have h1 := hε₀g g hg
      calc ε₀⁻¹ * (h⁻¹ * ((h * w' * h⁻¹)⁻¹ * (c * w * c⁻¹)) * h) * g
          = ε₀⁻¹ * ((h⁻¹ * ((h * w' * h⁻¹)⁻¹ * (c * w * c⁻¹)) * h) * g *
              (h⁻¹ * ((h * w' * h⁻¹)⁻¹ * (c * w * c⁻¹)) * h)⁻¹) *
              (h⁻¹ * ((h * w' * h⁻¹)⁻¹ * (c * w * c⁻¹)) * h) := by group
        _ = ε₀⁻¹ * (ε₀ * g * ε₀⁻¹) * (h⁻¹ * ((h * w' * h⁻¹)⁻¹ * (c * w * c⁻¹)) * h) := by rw [h1]
        _ = g * (ε₀⁻¹ * (h⁻¹ * ((h * w' * h⁻¹)⁻¹ * (c * w * c⁻¹)) * h)) := by group
    · group
  have hstep := step2 hSmall hC3 H fr hT hTW hPH hWH hCW hdC hdW
  calc conjSub c W = conjSub h (conjSub (h⁻¹ * c) W) := by
        rw [← conjSub_mul, mul_inv_cancel_left]
    _ = conjSub h W := by rw [hstep]

end Datum

theorem v3AE6OmegaHA_of (hQ8 : AE6ModelQ8) (hSmall : AE6ModelSmall) (hFW : AE6ModelFW)
    (hF : AE6ModelF) (hC1 : AE6ModelC1') (hC2 : AE6ModelC2) (hC3 : AE6ModelC3)
    (hW1 : V3AE6NoWt1 n) : V3AE6OmegaHA n := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y h H fr hx ε hrel hI hL J' hadj
  have hd := H.ex.1.datum
  have hQ8Ω := A6Gen.q8Omega_of_hyp H
  set Hε := Subgroup.closure (Set.range ε) with hHε
  have hMH : MGrp Ω[R] W ≤ Hε := le_trans le_sup_left hI
  have hPH : ae6P Ω[R] t ≤ Hε := (ae6P_le_ae6L _ _ _).trans hL
  have hWH : W ≤ Hε := W_le H hPH hMH
  have htH : t ∈ Hε := hPH (le_ae6P hd.mem hd.hz hd.hz.mem)
  let ε' : Fin 8 → ↥Hε := fun i => ⟨ε i, Subgroup.subset_closure ⟨i, rfl⟩⟩
  have hrel' : ∀ r ∈ A6.curtisRels, A6.curtisEval (List.ofFn ε') r = 1 := by
    intro r hr
    apply Hε.subtype_injective
    rw [← curtisEval_map, List.map_ofFn, map_one]
    exact hrel r hr
  have hgen' : Subgroup.closure (Set.range ε') = ⊤ := by
    have hrange : Set.range ε' = ((↑) : ↥Hε → Y) ⁻¹' Set.range ε := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, hi⟩
        exact ⟨i, Subtype.ext hi⟩
    rw [hrange]
    exact Subgroup.closure_closure_coe_preimage
  haveI : Nontrivial ↥Hε :=
    ⟨⟨⟨t, htH⟩, 1, fun h1 => hd.hz.ne_one (congrArg Subtype.val h1)⟩⟩
  obtain ⟨e₀⟩ := A6.curtisD42_recognition ε' hrel' hgen'
  obtain ⟨e, hT, hTW⟩ := exists_transp hQ8 hSmall hFW hC2 H fr hPH hWH e₀
  obtain ⟨W₁, hW₁, htW₁, hJ'D⟩ := exists_W_of_dstarAdj H hadj
  obtain ⟨c, hc, hcW⟩ := A6Gen.exists_cent_conj_W H hW₁ htW₁
  obtain ⟨g, hgH, hcg⟩ := conj_W_eq hSmall hF hC1 hC2 hC3 hW1 H fr hT hTW hPH hWH hc
  have hJ'' : conjSub g⁻¹ J' ∈ DSet Ω[R] W := by
    have h1 := hQ8Ω.conjSub_mem_DSet hJ'D g⁻¹
    rwa [← hcW, hcg, conjSub_inv_conjSub] at h1
  have hle : conjSub g⁻¹ J' ≤ Hε := by
    refine le_trans ?_ hMH
    unfold MGrp
    exact le_iSup₂_of_le _ hJ'' le_rfl
  calc J' = conjSub g (conjSub g⁻¹ J') := (conjSub_conjSub_inv g J').symm
    _ ≤ conjSub g Hε := conjSub_mono hle
    _ = Hε := conjSub_eq_self_of_mem hgH

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.A6jA
