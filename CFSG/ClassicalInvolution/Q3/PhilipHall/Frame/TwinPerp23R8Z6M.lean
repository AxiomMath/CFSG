module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8Z6Defs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZO2
public import CFSG.ClassicalInvolution.Sp62Rec.I1.KappaCount
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8Z6
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8Z6Kappa
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8Z6Main
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8Z6MLab
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZNormT
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZTwoI1
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZTwoP
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZTwoY
import CFSG.ClassicalInvolution.Sp62Rec.CECentZ5b
import CFSG.ClassicalInvolution.Sp62Rec.I1.TwinCentralizer
import CFSG.ClassicalInvolution.Sp62Rec.ModelCR1Basic
import CFSG.ClassicalInvolution.Sp62Rec.OddB
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinConnTransportLift

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Sp62Rec CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
  CFSG.ClassicalInvolution.Solomon73 CFSG.ClassicalInvolution.Solomon73.Yamaki

namespace Z6M

section Wr

theorem supportedOn_single (k : Fin 6) :
    SupportedOn (ofVec (Pi.single k (1 : ZMod 2))) ({k} : Set (Fin 6)) := by
  intro x hx
  refine ⟨?_, rfl⟩
  show (Pi.single k (1 : ZMod 2) : Fin 6 → ZMod 2) x = 0
  exact Pi.single_eq_of_ne (by simpa using hx) _

theorem single_comm_memAt {k : Fin 6} {β : Finset (Fin 6)} {hβ : β.card = 4} {b : Bool}
    (hk : k ∉ β) {x : Wr 6} (hx : x ∈ memAt β hβ b) :
    ofVec (Pi.single k (1 : ZMod 2)) * x = x * ofVec (Pi.single k (1 : ZMod 2)) := by
  refine comm_of_disjoint (supportedOn_single k) (supportedOn_of_mem_memAt hx) ?_
  rw [range_emb, Set.disjoint_singleton_left]
  exact hk

theorem wsum_single (k : Fin 6) : wsum (ofVec (Pi.single k (1 : ZMod 2))) = 1 := by
  show ∑ i, (Pi.single k (1 : ZMod 2) : Fin 6 → ZMod 2) i = 1
  simp

theorem ofVec_inv (v : Fin 6 → ZMod 2) : (ofVec v)⁻¹ = ofVec v :=
  Wr.ext (funext fun _ => rfl) inv_one

theorem perm_eq_swap_of_comm {β : Finset (Fin 6)} (hβ : β.card = 4) {w : Wr 6}
    (h1 : ∀ x ∈ memAt β hβ true, w * x = x * w) (h2 : ∀ x ∈ memAt β hβ false, w * x = x * w)
    (hodd : Equiv.Perm.sign w.perm = -1) {a b : Fin 6} (hab : a ≠ b) (ha : a ∉ β) (hb : b ∉ β)
    (hout : ∀ i, i ∉ β → i = a ∨ i = b) : w.perm = Equiv.swap a b := by
  have hB : ∀ c : Bool, ∀ x ∈ memBar β hβ c, mkQ 6 w * x * (mkQ 6 w)⁻¹ = x := by
    intro c x hx
    obtain ⟨m, hm, rfl⟩ := hx
    have hc : w * m = m * w := by
      cases c
      · exact h2 m hm
      · exact h1 m hm
    have h3 : mkQ 6 (w * m * w⁻¹) = mkQ 6 m := by rw [hc, mul_inv_cancel_right]
    simpa only [map_mul, map_inv] using h3
  obtain ⟨c, e', hw, he', hc⟩ := TwinThinPf10.exists_split (by norm_num) (by norm_num) β hβ w hB
  have hperm : w.perm = c.perm := by
    rw [hw, mul_perm]
    rcases he' with rfl | rfl
    · rw [one_perm, mul_one]
    · rw [zOf_perm, mul_one]
  have hfix : ∀ x ∈ β, c.perm x = x := by
    intro x hx
    refine (hc x ?_).2
    rw [Set.mem_compl_iff, not_not, range_emb]
    exact hx
  rcases ZTwo.perm_dichotomy hab ha hb hout c.perm hfix with h | h
  · rw [hperm, h, Equiv.Perm.sign_one] at hodd
    exact absurd hodd (by decide)
  · rw [hperm, h]

theorem comm_single_not_mem_piSub {a b : Fin 6} (hab : a ≠ b) {w : Wr 6}
    (hw : w.perm = Equiv.swap a b) {i : Fin 6} (hia : i ≠ a) (hib : i ≠ b) :
    ofVec (Pi.single a (1 : ZMod 2)) * w * (ofVec (Pi.single a (1 : ZMod 2)))⁻¹ * w⁻¹ ∉
      piSub 6 := by
  have hvec : ∀ j, (ofVec (Pi.single a (1 : ZMod 2)) * w * (ofVec (Pi.single a (1 : ZMod 2)))⁻¹ *
      w⁻¹).vec j = (Pi.single a 1 : Fin 6 → ZMod 2) j +
        (Pi.single a 1 : Fin 6 → ZMod 2) (Equiv.swap a b j) := by
    intro j
    have e1 : ofVec (Pi.single a (1 : ZMod 2)) * w * (ofVec (Pi.single a (1 : ZMod 2)))⁻¹ * w⁻¹ =
        ofVec (Pi.single a (1 : ZMod 2)) * (w * ofVec (Pi.single a (1 : ZMod 2)) * w⁻¹) := by
      rw [ofVec_inv]
      group
    rw [e1, TwinThinPf10.conj_ofVec, hw, Equiv.symm_swap]
    rfl
  intro hX
  rcases mem_piSub.mp hX with h | h
  · have h1 := hvec a
    rw [h, Equiv.swap_apply_left, Pi.single_eq_same, Pi.single_eq_of_ne hab.symm, one_vec] at h1
    simp at h1
  · have h1 := hvec i
    rw [h, Equiv.swap_apply_of_ne_of_ne hia hib, Pi.single_eq_of_ne hia] at h1
    simp [allOnes] at h1

end Wr

section Odd

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem oddC_eq_bot (hT : Thm4RTwinBelow 3 n) (hTwo : P23Two n) (hα : P23Alpha n)
    (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n) (hc : P23Cfg n Y R S t K' W u e g)
    (hno : ¬ SecNoExit R e) (hZ : u * e ∈ zStarOf (rLayer (Om R) u)) (hAE : SecAE R e 6) :
    classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y)) = ⊥ := by
  have hC := CoreData.of_S hc.std.perp.core
  have hTwo' := hTwo Y R S t K' W u e g hc
  have hαb : alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥ :=
    p23_alpha_eq_bot hc hTwo' (hα Y R S t K' W u e g hc (Or.inl hZ)).1
      ⟨p23E8Z_cu_le_normalizer_alpha hT hα hc hZ,
        p23E8ZNormT_of_alpha hT hα hcit hP Y R S t K' W u e g hc hno hZ hAE⟩
  have heq := p23E8Z_oddCoreIn_eq hT hc hZ hαb
  set N : Subgroup Y := oddCoreIn (Subgroup.centralizer ({t} : Set Y)) with hN
  have hnorm_of : ∀ x : Y, (∀ y ∈ N, x * y * x⁻¹ ∈ N) → (∀ y ∈ N, x⁻¹ * y * x ∈ N) →
      x ∈ Subgroup.normalizer (N : Set Y) := by
    intro x h1 h2
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => h1 h hh, fun hh => ?_⟩
    have := h2 _ hh
    simpa [mul_assoc] using this
  have hCt : Subgroup.centralizer ({t} : Set Y) ≤ Subgroup.normalizer (N : Set Y) := fun x hx =>
    hnorm_of x (fun y hy => conj_mem_oddCoreIn hx hy)
      (fun y hy => by
        have := conj_mem_oddCoreIn (Subgroup.inv_mem _ hx) hy
        simpa using this)
  have hCu : Subgroup.centralizer ({u} : Set Y) ≤ Subgroup.normalizer (N : Set Y) := fun x hx =>
    hnorm_of x (fun y hy => by rw [heq] at hy ⊢; exact conj_mem_oddCoreIn hx hy)
      (fun y hy => by
        rw [heq] at hy ⊢
        have := conj_mem_oddCoreIn (Subgroup.inv_mem _ hx) hy
        simpa using this)
  have htop : Subgroup.normalizer (N : Set Y) = ⊤ := by
    rw [eq_top_iff, ← hTwo']
    exact sup_le hCu hCt
  have hNn : N.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  have hle : N ≤ classicalInvolutionOddCore Y := le_sSup ⟨hNn, odd_card_oddCoreIn _⟩
  rw [hC.oddFree] at hle
  exact TwinConnT.classicalOddCore_eq_bot_of_oddCoreIn (le_bot_iff.mp hle)

end Odd

section Glue

variable {Y : Type} [Group Y] [Finite Y]

theorem piC_injective {C : Subgroup Y} (h : classicalInvolutionOddCore ↥C = ⊥) :
    Function.Injective (F7I.piC C) :=
  (MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk']; exact h)

theorem comm_of_piC {C L : Subgroup Y} (hinj : Function.Injective (F7I.piC C)) (hLC : L ≤ C)
    {m : ↥C} (h : ∀ x ∈ (L.subgroupOf C).map (F7I.piC C), F7I.piC C m * x = x * F7I.piC C m) :
    ∀ k ∈ L, (m : Y) * k = k * m := by
  intro k hk
  have h1 := h (F7I.piC C ⟨k, hLC hk⟩) ⟨⟨k, hLC hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
  rw [← map_mul, ← map_mul] at h1
  exact congrArg Subtype.val (hinj h1)

theorem piC_comm_of_comm {C L : Subgroup Y} {m : ↥C} (h : ∀ k ∈ L, (m : Y) * k = k * m) :
    ∀ x ∈ (L.subgroupOf C).map (F7I.piC C), F7I.piC C m * x = x * F7I.piC C m := by
  rintro _ ⟨k, hk, rfl⟩
  rw [← map_mul, ← map_mul]
  exact congrArg (F7I.piC C) (Subtype.ext (h k (Subgroup.mem_subgroupOf.mp hk)))

theorem coreAt_eq_self {e : Y} {J : Subgroup Y} (h2 : IsPGroup 2 J)
    (hJe : J ≤ Subgroup.centralizer ({e} : Set Y)) : TwinADescent.coreAt e J = J := by
  show tightCore (J ⊓ Subgroup.centralizer ({e} : Set Y)) = J
  rw [inf_eq_left.mpr hJe]
  exact tightCore_eq_of_isPGroup h2

theorem I1Action.card_B
    {z e : Y} {E B : Subgroup Y}
    {f : ↥E →* Wr 6} {Θ : ↥Sp62Rec.I1.Wsub ≃* ↥Hhat} {φ : ↥B →* ↥Hhat}
    (D : I1Action z e E B f Θ φ) (hO : oddCoreIn E = ⊥) : Nat.card B = 23040 := by
  have hker : φ.ker = ⊥ := by
    rw [D.φ_ker, hO]
    exact Subgroup.bot_subgroupOf _
  rw [← card_Hhat]
  exact Nat.card_eq_of_bijective φ ⟨(MonoidHom.ker_eq_bot_iff φ).mp hker, D.φ_surj⟩

theorem I1Action.exists_psi_onto {z e : Y} {E B : Subgroup Y}
    {f : ↥E →* Wr 6} {Θ : ↥Sp62Rec.I1.Wsub ≃* ↥Hhat} {φ : ↥B →* ↥Hhat}
    (D : I1Action z e E B f Θ φ) :
    ∃ Ψ : ↥B →* Wr 6, (∀ b, Ψ b ∈ Sp62Rec.I1.Wsub) ∧
      (∀ w ∈ Sp62Rec.I1.Wsub, ∃ b, Ψ b = w) ∧
      (∀ (b : Y) (hb : b ∈ B), ActsOnE f b (Ψ ⟨b, hb⟩)) ∧
      ∀ (x : Y) (hx : x ∈ E), Ψ ⟨x, D.E_le_B hx⟩ = f ⟨x, hx⟩ := by
  let Ψ : ↥B →* Wr 6 := Sp62Rec.I1.Wsub.subtype.comp (Θ.symm.toMonoidHom.comp φ)
  have hΨ : ∀ b : ↥B, Ψ b = ((Θ.symm (φ b) : ↥Sp62Rec.I1.Wsub) : Wr 6) := fun b => rfl
  refine ⟨Ψ, fun b => (Θ.symm (φ b)).2, ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨b, hb⟩ := D.φ_surj (Θ ⟨w, hw⟩)
    exact ⟨b, by rw [hΨ, hb, MulEquiv.symm_apply_apply]⟩
  · intro b hb x hx hx'
    have e1 : φ ⟨b * x * b⁻¹, D.E_le_B hx'⟩ =
        φ ⟨b, hb⟩ * φ ⟨x, D.E_le_B hx⟩ * (φ ⟨b, hb⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    obtain ⟨hm, h1⟩ := D.φ_f x hx
    obtain ⟨hm', h2⟩ := D.φ_f _ hx'
    rw [h1, h2] at e1
    have e2 := congrArg Θ.symm e1
    simp only [map_mul, map_inv, MulEquiv.symm_apply_apply] at e2
    exact congrArg Subtype.val e2
  · intro x hx
    obtain ⟨hm, h1⟩ := D.φ_f x hx
    rw [hΨ, h1, MulEquiv.symm_apply_apply]

theorem not_onto_of_gens {S : Set Y} {E : Subgroup Y} (Ψ : ↥(Subgroup.closure S ⊔ E) →* Wr 6)
    (hΨs : ∀ w ∈ Sp62Rec.I1.Wsub, ∃ b, Ψ b = w)
    (hS : ∀ b : ↥(Subgroup.closure S ⊔ E), (b : Y) ∈ S → Ψ b ∈ aeSub 6)
    (hE : ∀ b : ↥(Subgroup.closure S ⊔ E), (b : Y) ∈ E → Ψ b ∈ aeSub 6) : False := by
  have hall : Subgroup.closure S ⊔ E ≤
      ((aeSub 6).comap Ψ).map (Subgroup.closure S ⊔ E).subtype := by
    refine sup_le ?_ ?_
    · rw [Subgroup.closure_le]
      intro x hx
      exact ⟨⟨x, Subgroup.mem_sup_left (Subgroup.subset_closure hx)⟩, hS _ hx, rfl⟩
    · intro x hx
      exact ⟨⟨x, Subgroup.mem_sup_right hx⟩, hE _ hx, rfl⟩
  obtain ⟨b, hb⟩ := hΨs (ofPerm (Equiv.swap (0 : Fin 6) 1))
    (Sp62Rec.I1.mem_Wsub.mpr (Sp62Rec.I1.wsum_ofPerm _))
  obtain ⟨b', hb', hbb'⟩ := hall b.2
  have hb'b : b' = b := Subtype.ext hbb'
  rw [hb'b] at hb'
  have h1 : Ψ b ∈ aeSub 6 := hb'
  rw [hb] at h1
  have h2 := (mem_aeSub.mp h1).2
  rw [show (ofPerm (Equiv.swap (0 : Fin 6) 1)).perm = Equiv.swap 0 1 from rfl,
    Equiv.Perm.sign_swap (by decide)] at h2
  exact absurd h2 (by decide)

theorem card_centralizer_le_of_acts {e : Y} {E : Subgroup Y} {f : ↥E →* Wr 6}
    (H : KappaHyp e E f) (V : Subgroup (Wr 6))
    (hV : ∀ h ∈ Subgroup.centralizer ({e} : Set Y), ∀ w : Wr 6, ActsOnE f h w → w ∈ V) :
    Nat.card (Subgroup.centralizer ({e} : Set Y)) ≤ Nat.card V := by
  let Γ : Subgroup (Y × Wr 6) :=
    { carrier := {p | p.1 ∈ Subgroup.centralizer ({e} : Set Y) ∧ ActsOnE f p.1 p.2}
      mul_mem' := fun {a b} ha hb =>
        ⟨Subgroup.mul_mem _ ha.1 hb.1, ActsOnE.mul H.normal hb.1 ha.2 hb.2⟩
      one_mem' := ⟨Subgroup.one_mem _, ActsOnE.one⟩
      inv_mem' := fun {a} ha => ⟨Subgroup.inv_mem _ ha.1, ha.2.inv⟩ }
  have hmem : ∀ x : Y × Wr 6, x ∈ Γ ↔
      x.1 ∈ Subgroup.centralizer ({e} : Set Y) ∧ ActsOnE f x.1 x.2 := fun x => Iff.rfl
  let p : ↥Γ →* Y := (MonoidHom.fst Y (Wr 6)).comp Γ.subtype
  let q : ↥Γ →* Wr 6 := (MonoidHom.snd Y (Wr 6)).comp Γ.subtype
  have hp_range : p.range = Subgroup.centralizer ({e} : Set Y) := by
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      exact ((hmem _).mp x.2).1
    · intro hg
      obtain ⟨w, hw⟩ := H.kappa g hg
      exact ⟨⟨(g, w), (hmem _).mpr ⟨hg, hw⟩⟩, rfl⟩
  have hker : ∀ x : ↥p.ker, ((x : ↥Γ) : Y × Wr 6).2 ∈ piSub 6 := by
    intro x
    have h1 : ((x : ↥Γ) : Y × Wr 6).1 = 1 := x.2
    obtain ⟨-, hact⟩ := (hmem _).mp (x : ↥Γ).2
    rw [h1] at hact
    have := ActsOnE.unique H.range (fun x hx => by simpa using hx) ActsOnE.one hact
    simpa using this
  have hp_ker : Nat.card p.ker = 2 := by
    rw [← card_piSub]
    refine Nat.card_eq_of_bijective (fun x => ⟨((x : ↥Γ) : Y × Wr 6).2, hker x⟩) ⟨?_, ?_⟩
    · intro x y hxy
      have h2 : ((x : ↥Γ) : Y × Wr 6).2 = ((y : ↥Γ) : Y × Wr 6).2 := congrArg Subtype.val hxy
      have h1x : ((x : ↥Γ) : Y × Wr 6).1 = 1 := x.2
      have h1y : ((y : ↥Γ) : Y × Wr 6).1 = 1 := y.2
      exact Subtype.ext (Subtype.ext (Prod.ext (by rw [h1x, h1y]) h2))
    · intro w
      have hact : ActsOnE f 1 w.1 := by
        rcases w.2 with h | h
        · rw [h]; exact ActsOnE.one
        · rw [h]; exact ActsOnE.pi
      exact ⟨⟨⟨(1, w.1), (hmem _).mpr ⟨Subgroup.one_mem _, hact⟩⟩, rfl⟩, rfl⟩
  have hker2 : ∀ x : ↥q.ker, ((x : ↥Γ) : Y × Wr 6).1 ∈ Subgroup.zpowers e := by
    intro x
    have h1 : ((x : ↥Γ) : Y × Wr 6).2 = 1 := x.2
    obtain ⟨hC', hact⟩ := (hmem _).mp (x : ↥Γ).2
    rw [h1] at hact
    exact H.mem_zpowers_of_acts hC' hact
  have hq_ker : Nat.card q.ker = 2 := by
    rw [← H.card_zpowers]
    refine Nat.card_eq_of_bijective (fun x => ⟨((x : ↥Γ) : Y × Wr 6).1, hker2 x⟩) ⟨?_, ?_⟩
    · intro x y hxy
      have h2 : ((x : ↥Γ) : Y × Wr 6).1 = ((y : ↥Γ) : Y × Wr 6).1 := congrArg Subtype.val hxy
      have h1x : ((x : ↥Γ) : Y × Wr 6).2 = 1 := x.2
      have h1y : ((y : ↥Γ) : Y × Wr 6).2 = 1 := y.2
      exact Subtype.ext (Subtype.ext (Prod.ext h2 (by rw [h1x, h1y])))
    · intro g
      exact ⟨⟨⟨(g.1, 1), (hmem _).mpr ⟨H.zpowers_le g.2, H.acts_one_of_mem_zpowers g.2⟩⟩,
        rfl⟩, rfl⟩
  have hq_range : q.range ≤ V := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨hC', hact⟩ := (hmem _).mp x.2
    exact hV _ hC' _ hact
  have h1 := Subgroup.card_ker_mul_card_range p
  have h2 := Subgroup.card_ker_mul_card_range q
  rw [hp_ker, hp_range] at h1
  rw [hq_ker] at h2
  have h3 := Subgroup.card_le_of_le hq_range
  omega

theorem card_centralizer_le {e : Y} {E : Subgroup Y} {f : ↥E →* Wr 6} (H : KappaHyp e E f)
    (hw : ∀ h ∈ Subgroup.centralizer ({e} : Set Y), ∀ w : Wr 6, ActsOnE f h w → wsum w = 0) :
    Nat.card (Subgroup.centralizer ({e} : Set Y)) ≤ 23040 := by
  rw [← Sp62Rec.I1.card_Wsub]
  exact card_centralizer_le_of_acts H Sp62Rec.I1.Wsub fun h hh w hact =>
    Sp62Rec.I1.mem_Wsub.mpr (hw h hh w hact)

theorem wsum_eq_zero_of_M {e y : Y} {E B K K' : Subgroup Y} {f : ↥E →* Wr 6}
    (hnormal : ∀ g ∈ Subgroup.centralizer ({e} : Set Y), ∀ x ∈ E, g * x * g⁻¹ ∈ E)
    (hinj : Function.Injective f) (hrange : f.range = aeSub 6)
    (Ψ : ↥B →* Wr 6) (hΨW : ∀ b, Ψ b ∈ Sp62Rec.I1.Wsub)
    (hΨs : ∀ w ∈ Sp62Rec.I1.Wsub, ∃ b : ↥B, Ψ b = w)
    (hBC : B ≤ Subgroup.centralizer ({e} : Set Y))
    (hΨact : ∀ (b : Y) (hb : b ∈ B), ActsOnE f b (Ψ ⟨b, hb⟩))
    (hKE : K ≤ E) (hK'E : K' ≤ E) {β : Finset (Fin 6)} (hβ : β.card = 4) {b₀ : Bool}
    (hlab : (K.subgroupOf E).map f = memAt β hβ b₀)
    (hlab' : (K'.subgroupOf E).map f = memAt β hβ (!b₀))
    (hyB : y ∈ B) (hyK : ∀ k ∈ K, y * k = k * y) (hyK' : ∀ k ∈ K', y * k = k * y)
    (hyM : ∀ s ∈ Subgroup.centralizer ({e} : Set Y), (∀ k ∈ K, s * k = k * s) →
      (∀ k ∈ K', s * k = k * s) → s * y = y * s)
    (hyodd : Ψ ⟨y, hyB⟩ ∉ aeSub 6) :
    ∀ h ∈ Subgroup.centralizer ({e} : Set Y), ∀ w : Wr 6, ActsOnE f h w → wsum w = 0 := by
  intro h hh w hw
  by_contra hne
  have hw1 : wsum w = 1 := by
    have : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
    exact this _ hne
  obtain ⟨a, a', haa', ha, ha', hout⟩ := ZTwo.exists_compl_pair hβ
  set v : Wr 6 := ofVec (Pi.single a (1 : ZMod 2)) with hv
  have hvW : w⁻¹ * v ∈ Sp62Rec.I1.Wsub := by
    rw [Sp62Rec.I1.mem_Wsub, wsum_mul, wsum_inv, hw1, hv, wsum_single]
    decide
  obtain ⟨bb, hbb⟩ := hΨs _ hvW
  have hbbC : (bb : Y) ∈ Subgroup.centralizer ({e} : Set Y) := hBC bb.2
  have hsC : h * (bb : Y) ∈ Subgroup.centralizer ({e} : Set Y) := Subgroup.mul_mem _ hh hbbC
  have hsact : ActsOnE f (h * (bb : Y)) v := by
    have h1 := ActsOnE.mul hnormal hbbC hw (hΨact (bb : Y) bb.2)
    have h2 : Ψ ⟨(bb : Y), bb.2⟩ = w⁻¹ * v := hbb
    rwa [h2, mul_inv_cancel_left] at h1
  have hcent : ∀ (L : Subgroup Y) (c : Bool), L ≤ E → (L.subgroupOf E).map f = memAt β hβ c →
      ∀ k ∈ L, h * (bb : Y) * k = k * (h * (bb : Y)) := by
    intro L c hLE hL k hk
    have hkE := hLE hk
    have hsk := hnormal _ hsC k hkE
    have h1 := hsact k hkE hsk
    have hfk : f ⟨k, hkE⟩ ∈ memAt β hβ c := by
      rw [← hL]
      exact ⟨⟨k, hkE⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
    rw [hv, single_comm_memAt ha hfk, mul_inv_cancel_right] at h1
    have h2 := congrArg Subtype.val (hinj h1)
    calc h * (bb : Y) * k = (h * (bb : Y) * k * (h * (bb : Y))⁻¹) * (h * (bb : Y)) := by group
      _ = k * (h * (bb : Y)) := by rw [show h * (bb : Y) * k * (h * (bb : Y))⁻¹ = k from h2]
  have hsy := hyM _ hsC (hcent K b₀ hKE hlab) (hcent K' (!b₀) hK'E hlab')
  have hyC : y ∈ Subgroup.centralizer ({e} : Set Y) := hBC hyB
  have hwy : ∀ (L : Subgroup Y) (c : Bool), L ≤ E → (L.subgroupOf E).map f = memAt β hβ c →
      (∀ k ∈ L, y * k = k * y) → ∀ x ∈ memAt β hβ c, Ψ ⟨y, hyB⟩ * x = x * Ψ ⟨y, hyB⟩ := by
    intro L c hLE hL hyL x hx
    rw [← hL] at hx
    obtain ⟨⟨k, hkE⟩, hk, rfl⟩ := hx
    have hk' : k ∈ L := Subgroup.mem_subgroupOf.mp hk
    have hyk := hnormal y hyC k hkE
    have h1 := hΨact y hyB k hkE hyk
    have h2 : (⟨y * k * y⁻¹, hyk⟩ : ↥E) = ⟨k, hkE⟩ :=
      Subtype.ext (show y * k * y⁻¹ = k by rw [hyL k hk', mul_inv_cancel_right])
    rw [h2] at h1
    calc Ψ ⟨y, hyB⟩ * f ⟨k, hkE⟩
        = (Ψ ⟨y, hyB⟩ * f ⟨k, hkE⟩ * (Ψ ⟨y, hyB⟩)⁻¹) * Ψ ⟨y, hyB⟩ := by group
      _ = f ⟨k, hkE⟩ * Ψ ⟨y, hyB⟩ := by rw [← h1]
  have hwyb := hwy K b₀ hKE hlab hyK
  have hwyb' := hwy K' (!b₀) hK'E hlab' hyK'
  have hwyt : ∀ x ∈ memAt β hβ true, Ψ ⟨y, hyB⟩ * x = x * Ψ ⟨y, hyB⟩ := by
    cases b₀
    · exact hwyb'
    · exact hwyb
  have hwyf : ∀ x ∈ memAt β hβ false, Ψ ⟨y, hyB⟩ * x = x * Ψ ⟨y, hyB⟩ := by
    cases b₀
    · exact hwyb
    · exact hwyb'
  have hsign : Equiv.Perm.sign (Ψ ⟨y, hyB⟩).perm = -1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Ψ ⟨y, hyB⟩).perm) with h1 | h1
    · exact absurd (mem_aeSub.mpr ⟨Sp62Rec.I1.mem_Wsub.mp (hΨW _), h1⟩) hyodd
    · exact h1
  have hperm := perm_eq_swap_of_comm hβ hwyt hwyf hsign haa' ha ha' hout
  have hact : ActsOnE f (h * (bb : Y) * y * (h * (bb : Y))⁻¹ * y⁻¹)
      (v * Ψ ⟨y, hyB⟩ * v⁻¹ * (Ψ ⟨y, hyB⟩)⁻¹) :=
    ActsOnE.mul hnormal (Subgroup.inv_mem _ hyC)
      (ActsOnE.mul hnormal (Subgroup.inv_mem _ hsC)
        (ActsOnE.mul hnormal hyC hsact (hΨact y hyB)) hsact.inv) (hΨact y hyB).inv
  have h1 : h * (bb : Y) * y * (h * (bb : Y))⁻¹ * y⁻¹ = 1 := by
    rw [hsy]
    group
  rw [h1] at hact
  have hpi := ActsOnE.unique hrange (fun x hx => by simpa using hx) ActsOnE.one hact
  rw [inv_one, one_mul] at hpi
  obtain ⟨i, hi⟩ : ∃ i, i ∈ β := Finset.card_pos.mp (by rw [hβ]; norm_num)
  have hia : i ≠ a := fun h => ha (h ▸ hi)
  have hia' : i ≠ a' := fun h => ha' (h ▸ hi)
  exact comm_single_not_mem_piSub haa' hperm hia hia' hpi

end Glue

end Z6M

variable {n : ℕ}

private theorem p23E8Z_M_core (hT : Thm4RTwinBelow 3 n) (hTwo : P23Two n) (hα : P23Alpha n)
    (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n) {Y : Type} [Group Y] [Finite Y]
    {R : Subgroup Y} {S : Sylow 2 R} {t : Y} {K' W : Subgroup Y} {u e g : Y}
    (hc : P23Cfg n Y R S t K' W u e g) (hno : ¬ SecNoExit R e)
    (hZs : u * e ∈ zStarOf (rLayer (Om R) u)) (hAE : SecAE R e 6) :
    ∃ c' ∈ Subgroup.centralizer ({t} : Set Y), c' * e * c'⁻¹ ≠ e ∧
      (c' * e * c'⁻¹) * e = e * (c' * e * c'⁻¹) ∧
      I1In R t e (Subgroup.closure ({e, t, c' * e * c'⁻¹} : Set Y)) ∧
      (∀ s : Y, (∀ k ∈ tightCore R, s * k = k * s) → (∀ k ∈ K', s * k = k * s) →
        s * e = e * s ∧ s * (c' * e * c'⁻¹) = (c' * e * c'⁻¹) * s) ∧
      ∃ (f : ↥(rLayer (Om R) e) →* Wr 6) (Θ : ↥Sp62Rec.I1.Wsub ≃* ↥Hhat)
        (φ : ↥(Subgroup.closure ({e, t, c' * e * c'⁻¹} : Set Y) ⊔ rLayer (Om R) e) →* ↥Hhat),
        I1Action t e (rLayer (Om R) e)
          (Subgroup.closure ({e, t, c' * e * c'⁻¹} : Set Y) ⊔ rLayer (Om R) e) f Θ φ ∧
        oddCoreIn (Subgroup.centralizer ({e} : Set Y)) = ⊥ ∧ Function.Injective f ∧
        ∀ h ∈ Subgroup.centralizer ({e} : Set Y), ∀ w : Wr 6, ActsOnE f h w → wsum w = 0 := by
  classical
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hzt : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hzt hc.std.hK'
  have hte : t ≠ e := fun h => e_not_mem_sup hc (h ▸ Subgroup.mem_sup_left hzt.mem)
  have hOC := Z6M.oddC_eq_bot hT hTwo hα hcit hP hc hno hZs hAE
  have hOCt : oddCoreIn (Subgroup.centralizer ({t} : Set Y)) = ⊥ :=
    TwinConnT.oddCoreIn_eq_bot_of_classicalOddCore hOC
  have hinj := Z6M.piC_injective hOC
  have heC : e ∈ Subgroup.centralizer ({t} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (ZTwo.e_comm_t hc)
  have htC : t ∈ Subgroup.centralizer ({t} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  obtain ⟨-, -, h8A, h8B, -, -, -, heA, heB, -⟩ := p23_twin_q8 hc rfl htC heC
  have hKC : tightCore R ≤ Subgroup.centralizer ({t} : Set Y) := le_centralizer_of_unique hzt
  have hK'C : K' ≤ Subgroup.centralizer ({t} : Set Y) := le_centralizer_of_unique hz'
  have heK : ∀ k ∈ tightCore R, e * k = k * e := Z6M.comm_of_piC hinj hKC heA
  have heK' : ∀ k ∈ K', e * k = k * e := Z6M.comm_of_piC hinj hK'C heB
  have hcard : ∀ L : Subgroup Y, L ≤ Subgroup.centralizer ({t} : Set Y) →
      Nat.card ((L.subgroupOf (Subgroup.centralizer ({t} : Set Y))).map
        (F7I.piC (Subgroup.centralizer ({t} : Set Y)))) = 8 → IsPGroup 2 L := by
    intro L hL h8
    rw [Subgroup.card_map_of_injective hinj,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL).toEquiv] at h8
    exact IsPGroup.of_card (n := 3) (by rw [h8]; norm_num)
  have hK2 := hcard _ hKC h8A
  have hK'2 := hcard _ hK'C h8B
  have hKe : tightCore R ≤ Subgroup.centralizer ({e} : Set Y) := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mpr (heK k hk).symm
  have hK'e : K' ≤ Subgroup.centralizer ({e} : Set Y) := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mpr (heK' k hk).symm
  have hcore := Z6M.coreAt_eq_self hK2 hKe
  have hcore' := Z6M.coreAt_eq_self hK'2 hK'e
  have hle : ∀ {J : Subgroup Y}, J ∈ tqMembers3 (Om R) e →
      TwinADescent.coreAt e J ≤ rLayer (Om R) e := by
    intro J hJ x hx
    rw [← ZTwo.hmap_of hc]
    exact ⟨⟨x, TwinADescent.coreAt_le_centralizer e J hx⟩,
      TwinDisc.le_coreHull hJ (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hKE : tightCore R ≤ rLayer (Om R) e := hcore ▸ hle (ZTwo.twins_tq hc).1
  have hK'E : K' ≤ rLayer (Om R) e := hcore' ▸ hle (ZTwo.twins_tq hc).2
  have hZcu := R56.p23_zstar_cu hT hc hZs
  have hMe : ∀ s : Y, (∀ k ∈ tightCore R, s * k = k * s) → (∀ k ∈ K', s * k = k * s) →
      s * e = e * s := by
    intro s hsK hsK'
    have hsC : s ∈ Subgroup.centralizer ({t} : Set Y) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hsK t hzt.mem)
    have h1 := p23MBar_proved hcit hP Y R S t K' W u e g hc hZcu ⟨e, heC⟩ rfl
      (F7I.piC _ ⟨s, hsC⟩) (Z6M.piC_comm_of_comm (m := ⟨s, hsC⟩) hsK)
      (Z6M.piC_comm_of_comm (m := ⟨s, hsC⟩) hsK')
    rw [← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (hinj h1)
  have hconj : ∀ c ∈ Subgroup.centralizer ({t} : Set Y), ∀ s : Y,
      (∀ k ∈ tightCore R, s * k = k * s) → (∀ k ∈ K', s * k = k * s) →
      (∀ k ∈ tightCore R, c⁻¹ * s * c * k = k * (c⁻¹ * s * c)) ∧
        (∀ k ∈ K', c⁻¹ * s * c * k = k * (c⁻¹ * s * c)) := by
    intro c hcC s hsK hsK'
    have hsL : ∀ x : Y, (x ∈ tightCore R ∨ x ∈ K') → s * x = x * s := by
      rintro x (hx | hx)
      · exact hsK x hx
      · exact hsK' x hx
    have hmem : ∀ (H : Subgroup Y) (x : Y), x ∈ H → c * x * c⁻¹ ∈ conjSub c H := by
      intro H x hx
      rw [mem_conjSub_iff]
      have e1 : c⁻¹ * (c * x * c⁻¹) * c = x := by group
      rw [e1]
      exact hx
    have key : ∀ x : Y, (c * x * c⁻¹ ∈ tightCore R ∨ c * x * c⁻¹ ∈ K') →
        c⁻¹ * s * c * x = x * (c⁻¹ * s * c) := by
      intro x hx
      have h1 := hsL _ hx
      calc c⁻¹ * s * c * x = c⁻¹ * (s * (c * x * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * x * c⁻¹) * s) * c := by rw [h1]
        _ = x * (c⁻¹ * s * c) := by group
    rcases p23_conj_twins hc hcC with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨fun k hk => key k (Or.inl (h1 ▸ hmem _ k hk)),
        fun k hk => key k (Or.inr (h2 ▸ hmem _ k hk))⟩
    · exact ⟨fun k hk => key k (Or.inr (h1 ▸ hmem _ k hk)),
        fun k hk => key k (Or.inl (h2 ▸ hmem _ k hk))⟩
  obtain ⟨c', hc'C, hyc, hne, hfield⟩ := ZTwo.exists_y hT hcit hP hTwo hα hc hno hZs hAE
  obtain ⟨D⟩ := ZTwo.exists_cover hc hAE
  set y := c' * e * c'⁻¹ with hydef
  have hyC : y ∈ Subgroup.centralizer ({e} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hyc
  have hy2 : y * y = 1 := by
    calc y * y = c' * (e * e) * c'⁻¹ := by rw [hydef]; group
      _ = 1 := by rw [hd.he2]; group
  have hct : c' * t * c'⁻¹ = t := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hc'C]
    group
  have hyt : y * t = t * y := by
    calc y * t = c' * e * c'⁻¹ * (c' * t * c'⁻¹) := by rw [hct]
      _ = c' * (e * t) * c'⁻¹ := by group
      _ = c' * (t * e) * c'⁻¹ := by rw [ZTwo.e_comm_t hc]
      _ = (c' * t * c'⁻¹) * (c' * e * c'⁻¹) := by group
      _ = t * y := by rw [hct]
  obtain ⟨β₁, hβ₁, w₁, hw₁, hz₁, hcase⟩ := ZTwo.y_cases hc D hyC hyt hfield
  have hodd₁ : Equiv.Perm.sign w₁.perm = -1 := by
    rcases hcase with hodd | hT1 | ⟨c₀, hc₀, hcen⟩
    · exact hodd
    · exfalso
      have hφ : ∀ q, D.φ (TwinExitPf6.secAut (Om R) e (ZTwo.hΩ_of hc) (ZTwo.hc2e_of hc)
          ⟨y, hyC⟩ q) = D.φ q := by
        intro q
        rw [hw₁ q, hT1, one_mul, inv_one, mul_one]
      have hid := ZTwo.eq_of_trivial_mod_ker D.perfect
        (TwinExitPf6.secAut (Om R) e (ZTwo.hΩ_of hc) (ZTwo.hc2e_of hc) ⟨y, hyC⟩) (fun q => by
          apply D.toAEData.ker_le
          rw [MonoidHom.mem_ker, map_mul, map_inv, hφ, inv_mul_cancel])
      exact ZTwo.false_of_trivial hc D hyC hy2 hne hid
    · exact (ZTwo.false_of_zv hT hc hZs D hc'C hyC hy2 hyt hw₁ hz₁ hc₀ hcen).elim
  obtain ⟨ρ, hρs, hρk⟩ := ZTwo.exists_rho_of_odd hc D hyC hy2 hw₁ hodd₁
  have hIH : I1In R t e (Subgroup.closure ({e, t, y} : Set Y)) :=
    i1In_of_zTwo hc hyt hyc hy2 hfield ⟨ρ, hρs, hρk⟩
  have hyM : ∀ s : Y, (∀ k ∈ tightCore R, s * k = k * s) → (∀ k ∈ K', s * k = k * s) →
      s * y = y * s := by
    intro s hsK hsK'
    obtain ⟨h1, h2⟩ := hconj c' hc'C s hsK hsK'
    have h3 := hMe _ h1 h2
    calc s * y = c' * ((c'⁻¹ * s * c') * e) * c'⁻¹ := by rw [hydef]; group
      _ = c' * (e * (c'⁻¹ * s * c')) * c'⁻¹ := by rw [h3]
      _ = y * s := by rw [hydef]; group
  have hc'iC : c'⁻¹ ∈ Subgroup.centralizer ({t} : Set Y) := Subgroup.inv_mem _ hc'C
  obtain ⟨hyK, hyK'⟩ := hconj c'⁻¹ hc'iC e (fun k hk => heK k hk) (fun k hk => heK' k hk)
  rw [inv_inv] at hyK hyK'
  have htK : ∀ k ∈ tightCore R, t * k = k * t := fun k hk =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hKC hk)).symm
  have htK' : ∀ k ∈ K', t * k = k * t := fun k hk =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hK'C hk)).symm
  have hZH : ∀ x ∈ Subgroup.closure ({e, t, y} : Set Y), ∀ l ∈ tightCore R ⊔ K', x * l = l * x := by
    intro x hx
    have hgen : ∀ z ∈ ({e, t, y} : Set Y), z ∈ Subgroup.centralizer
        ((tightCore R : Set Y) ∪ (K' : Set Y)) := by
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      have hzK : (∀ k ∈ tightCore R, z * k = k * z) ∧ (∀ k ∈ K', z * k = k * z) := by
        rcases hz with hz | hz | hz
        · rw [hz]; exact ⟨heK, heK'⟩
        · rw [hz]; exact ⟨htK, htK'⟩
        · rw [hz]; exact ⟨hyK, hyK'⟩
      rintro k (hk | hk)
      · exact (hzK.1 k hk).symm
      · exact (hzK.2 k hk).symm
    have hxM := (Subgroup.closure_le _).mpr hgen hx
    intro l hl
    have hle' : tightCore R ⊔ K' ≤ Subgroup.centralizer ({x} : Set Y) := by
      refine sup_le (fun k hk => ?_) (fun k hk => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp hxM k (Or.inl hk))
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp hxM k (Or.inr hk))
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle' hl)).symm
  have hcommH : ∀ x ∈ Subgroup.closure ({e, t, y} : Set Y), ∀ l ∈ tightCore R ⊔ K',
      x * l * x⁻¹ * l⁻¹ ∈ oddCoreIn (Subgroup.centralizer ({t} : Set Y)) := by
    intro x hx l hl
    rw [hZH x hx l hl, mul_inv_cancel_right, mul_inv_cancel]
    exact Subgroup.one_mem _
  obtain ⟨f, Θ, φ, DH, β, hβ, b₀, hlab, hlab'⟩ :=
    Z6M.i1_action_lab_final hc.std.perp hAE hIH (ZTwo.twins_tq hc).1 (ZTwo.twins_tq hc).2
      hc.std.hne hzt hz' hcommH
  rw [hcore] at hlab
  rw [hcore'] at hlab'
  have PH := DH.toI1Six
  obtain ⟨TB, hzT, hzc⟩ := PH.exists_sylow_B hzt.sq
  have hodd : oddCoreIn (Subgroup.centralizer ({e} : Set Y)) = ⊥ :=
    PH.oddCoreIn_centralizer_eq_bot TB hzT hzc hzt.sq hzt.ne_one hte hd.he2 hOCt
      (p23E8Z_e_mem_pCore hT hcit hP hc hZs hOCt) card_S0 card_Hhat eq_of_mem_center_S0
      Hhat_le_centralizer_alpha fun x hx => exists_four_conj hx
  have hfinj : Function.Injective f := by
    refine (MonoidHom.ker_eq_bot_iff f).mp ?_
    rw [DH.f_ker, DH.oddCoreIn_eq_bot hodd]
    exact Subgroup.bot_subgroupOf _
  obtain ⟨Ψ, hΨW, hΨs, hΨact, hΨE⟩ := Z6M.I1Action.exists_psi_onto DH
  have hyB : y ∈ Subgroup.closure ({e, t, y} : Set Y) ⊔ rLayer (Om R) e :=
    Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
  have hE0 : ∀ b : ↥(Subgroup.closure ({e, t, y} : Set Y) ⊔ rLayer (Om R) e),
      (b : Y) ∈ rLayer (Om R) e → Ψ b ∈ aeSub 6 := by
    intro b hb
    have h : Ψ b = f ⟨(b : Y), hb⟩ := hΨE (b : Y) hb
    rw [h, ← DH.f_range]
    exact ⟨_, rfl⟩
  have hyodd : Ψ ⟨y, hyB⟩ ∉ aeSub 6 := by
    intro hyae
    refine Z6M.not_onto_of_gens Ψ hΨs (fun b hb => ?_) hE0
    rcases hb with hb | hb | hb
    · exact hE0 b (by rw [hb]; exact DH.e_mem)
    · exact hE0 b (by rw [hb]; exact (ZTwo.t_e_mem_rLayer hc).1)
    · rw [show b = ⟨y, hyB⟩ from Subtype.ext (Set.mem_singleton_iff.mp hb)]
      exact hyae
  have hwsum := Z6M.wsum_eq_zero_of_M DH.normal_of_centralizer hfinj DH.f_range Ψ hΨW hΨs
    DH.B_le hΨact hKE hK'E hβ hlab hlab' hyB hyK hyK' (fun s _ hsK hsK' => hyM s hsK hsK') hyodd
  exact ⟨c', hc'C, hne, hyc, hIH, fun s hsK hsK' => ⟨hMe s hsK hsK', hyM s hsK hsK'⟩, f, Θ, φ,
    DH, hodd, hfinj, hwsum⟩

theorem p23E8Z_centralizer_e_le (hT : Thm4RTwinBelow 3 n) (hTwo : P23Two n)
    (hα : P23Alpha n) (hCE : P23E8ZCE n) :
    CIT3Below n → TL4.TightBelowRPlus 3 n →
    ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
      (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e →
        u * e ∈ zStarOf (rLayer (Om R) u) → SecAE R e 6 →
          ∀ Z : Subgroup Y, I1In R t e Z →
            Subgroup.centralizer ({e} : Set Y) ≤ Z ⊔ rLayer (Om R) e := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno hZs hAE Z hIZ
  have hd := hc.data
  obtain ⟨c', -, -, -, -, -, f, Θ, φ, DH, hodd, -, hwsum⟩ :=
    p23E8Z_M_core hT hTwo hα hcit hP hc hno hZs hAE
  have hCEE : Subgroup.centralizer (rLayer (Om R) e : Set Y) = Subgroup.zpowers e :=
    DH.toI1Six.centralizer_eq_zpowers_of_Z5b hodd hd.he2 hd.he1
      (hCE hcit hP Y R S t K' W u e g hc hno hZs hAE)
  have hcardC := Z6M.card_centralizer_le (DH.kappaHyp hodd hd.he2 hd.he1 hCEE) hwsum
  obtain ⟨fZ, ΘZ, φZ, DZ⟩ := i1_action_final hc.std.perp hAE hIZ
  have hcardZ := Z6M.I1Action.card_B DZ (DH.oddCoreIn_eq_bot hodd)
  exact (Subgroup.eq_of_le_of_card_ge DZ.B_le (by rw [hcardZ]; exact hcardC)).ge

theorem p23E8ZX_of_ce (hT : Thm4RTwinBelow 3 n) (hTwo : P23Two n) (hα : P23Alpha n)
    (hCE : P23E8ZCE n) : P23E8ZX n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno hZs hAE Z hI _ _ hbad
  exact absurd (p23E8Z_centralizer_e_le hT hTwo hα hCE hcit hP Y R S t K' W u e g hc hno hZs hAE
    Z hI) hbad

theorem p23E8ZSix_of_ce (hT : Thm4RTwinBelow 3 n) (hTwo : P23Two n) (hα : P23Alpha n)
    (hCE : P23E8ZCE n) : P23E8ZSix n :=
  p23E8ZSix_of_leaves hT hCE (p23E8ZX_of_ce hT hTwo hα hCE)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
