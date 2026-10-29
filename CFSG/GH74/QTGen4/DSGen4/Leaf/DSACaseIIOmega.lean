module

public import CFSG.GH74.QTGen4.DSGen4.LeafWrappers

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement

private theorem dsa2_dsOmega1_le {G : Type} [Group G] (X : Subgroup G) : dsOmega1 X ≤ X := by
  unfold dsOmega1
  exact (Subgroup.closure_le X).2 fun _ hx => hx.1

private theorem dsa2_centerOf_le {G : Type} [Group G] (X : Subgroup G) : centerOf X ≤ X :=
  fun _ hx => (Subgroup.mem_inf.mp hx).1

private theorem dsa2_mem_centerOf {G : Type} [Group G] {X : Subgroup G} {x : G} :
    x ∈ centerOf X ↔ x ∈ X ∧ ∀ y ∈ X, y * x = x * y := by
  simp only [centerOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, SetLike.mem_coe]

private theorem dsa2_mem_dsOmega1 {G : Type} [Group G] {X : Subgroup G} {x : G}
    (hx : x ∈ X) (hx2 : x ^ 2 = 1) : x ∈ dsOmega1 X :=
  Subgroup.subset_closure ⟨hx, hx2⟩

private theorem dsa2_mem_dsCentMod {G : Type} [Group G] {P L Q : Subgroup G} {x : G} :
    x ∈ dsCentMod P L Q ↔ x ∈ P ∧ x ∈ Subgroup.normalizer (Q : Set G) ∧ ∀ l ∈ L, ⁅x, l⁆ ∈ Q :=
  Iff.rfl

private theorem dsa2_le_normalizer_of_conj {G : Type} [Group G] {H X : Subgroup G}
    (h : ∀ g ∈ H, ∀ x ∈ X, g * x * g⁻¹ ∈ X) : H ≤ Subgroup.normalizer (X : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h g hg x hx, fun hx => ?_⟩
  have := h g⁻¹ (H.inv_mem hg) (g * x * g⁻¹) hx
  simpa [mul_assoc] using this

private theorem dsa2_le_normalizer_centralizer {G : Type} [Group G] {P L Y : Subgroup G}
    (hPL : P ≤ Subgroup.normalizer (L : Set G)) (hPY : P ≤ Subgroup.normalizer (Y : Set G)) :
    P ≤ Subgroup.normalizer ((Y ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
  refine dsa2_le_normalizer_of_conj fun g hg x hx => ?_
  obtain ⟨hxY, hxC⟩ := Subgroup.mem_inf.mp hx
  have hxc : ∀ h ∈ (L : Set G), h * x = x * h := Subgroup.mem_centralizer_iff.mp hxC
  refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hPY hg) x).mp hxY, ?_⟩
  refine Subgroup.mem_centralizer_iff.mpr fun l hl => ?_
  have hl' : g⁻¹ * l * g ∈ L := by
    refine (Subgroup.mem_normalizer_iff.mp (hPL hg) (g⁻¹ * l * g)).mpr ?_
    rw [show g * (g⁻¹ * l * g) * g⁻¹ = l by group]
    exact hl
  have hm := hxc _ hl'
  calc l * (g * x * g⁻¹) = g * ((g⁻¹ * l * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * l * g)) * g⁻¹ := by rw [hm]
    _ = g * x * g⁻¹ * l := by group

private theorem dsa2_le_normalizer_centMod {G : Type} [Group G] {P L Q Φ : Subgroup G}
    (hPL : P ≤ Subgroup.normalizer (L : Set G)) (hPQ : P ≤ Subgroup.normalizer (Q : Set G))
    (hPΦ : P ≤ Subgroup.normalizer (Φ : Set G)) :
    P ≤ Subgroup.normalizer ((Q ⊓ dsCentMod P L Φ : Subgroup G) : Set G) := by
  refine dsa2_le_normalizer_of_conj fun g hg x hx => ?_
  obtain ⟨hxQ, hxC⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨hxP, hxN, hxc⟩ := dsa2_mem_dsCentMod.mp hxC
  refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hPQ hg) x).mp hxQ, ?_⟩
  refine dsa2_mem_dsCentMod.mpr ⟨P.mul_mem (P.mul_mem hg hxP) (P.inv_mem hg), ?_, ?_⟩
  · exact (Subgroup.normalizer (Φ : Set G)).mul_mem
      ((Subgroup.normalizer (Φ : Set G)).mul_mem (hPΦ hg) hxN)
      ((Subgroup.normalizer (Φ : Set G)).inv_mem (hPΦ hg))
  · intro l hl
    have hl' : g⁻¹ * l * g ∈ L := by
      refine (Subgroup.mem_normalizer_iff.mp (hPL hg) (g⁻¹ * l * g)).mpr ?_
      rw [show g * (g⁻¹ * l * g) * g⁻¹ = l by group]
      exact hl
    have e : ⁅g * x * g⁻¹, l⁆ = g * ⁅x, g⁻¹ * l * g⁆ * g⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hPΦ hg) _).mp (hxc _ hl')

private theorem dsa2_le_centMod {G : Type} [Group G] {P L Q Φ : Subgroup G}
    (hLP : L ≤ P) (hPL : P ≤ Subgroup.normalizer (L : Set G))
    (hPΦ : P ≤ Subgroup.normalizer (Φ : Set G)) (hΦP : Φ ≤ P) (hΦQ : Φ ≤ Q) :
    Φ ≤ Q ⊓ dsCentMod P L Φ := by
  intro t ht
  refine Subgroup.mem_inf.mpr ⟨hΦQ ht, dsa2_mem_dsCentMod.mpr ⟨hΦP ht, hPΦ (hΦP ht), fun l hl => ?_⟩⟩
  have e : ⁅t, l⁆ = t * (l * t⁻¹ * l⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact Φ.mul_mem ht ((Subgroup.mem_normalizer_iff.mp (hPΦ (hLP hl)) t⁻¹).mp (Φ.inv_mem ht))

theorem leafDSACaseIIOmega [DSLeaf LeafDSANoField] [DSLeaf LeafZiStructure] [DSLeaf LeafZiChief] [DSLeaf LeafFrattiniChief] [DSLeaf LeafFaithfulA5] [DSLeaf LeafSylowS] : LeafDSACaseIIOmega := by
  intro G _ _ L1 L2 S h c2 _c1
  obtain ⟨-, hS2, hB⟩ := dsa_no_field h
  obtain ⟨hZne, hZZi, hZiY, hYab, hYcard, -, hPY⟩ :=
    zi_structure (⟨h.hyp, hB⟩ : ZSetting L1 L2 S).symm
  have hA5 : A5Par L2 (L2 ⊔ bigB L2 L1 S) := A5Par.of_hyp111R Finite4.gen4 h.hyp.symm h.ns2
  have hFC : A5Chief (L2 ⊔ bigB L2 L1 S) L2 (dsQ L2 L1 S) (dsFrattini (dsQ L2 L1 S)) :=
    frattini_chief hA5
  have hQP : dsQ L2 L1 S ≤ L2 ⊔ bigB L2 L1 S := Subgroup.map_subtype_le _
  have hΦQ : dsFrattini (dsQ L2 L1 S) ≤ dsQ L2 L1 S := Subgroup.map_subtype_le _
  have hQS : dsQ L2 L1 S ≤ S := by
    have h' : dsQ L2 L1 S ≤ (S ⊓ L2) ⊔ dsQ L2 L1 S := le_sup_right
    rwa [← hS2] at h'
  have hYQ : dsOmega1 (centerOf (dsQ L2 L1 S)) ≤ dsQ L2 L1 S :=
    (dsa2_dsOmega1_le (centerOf (dsQ L2 L1 S))).trans (dsa2_centerOf_le (dsQ L2 L1 S))
  have hZY : dsZ S ≤ dsOmega1 (centerOf (dsQ L2 L1 S)) := hZZi.trans hZiY
  have hZQ : dsZ S ≤ dsQ L2 L1 S := hZY.trans hYQ
  have hZc : ∀ z ∈ dsZ S, ∀ l ∈ L2, l * z = z * l := by
    intro z hz l hl
    have h1 : ⁅z, l⁆ = 1 := by
      have hmem := Subgroup.commutator_mem_commutator (hZZi hz) hl
      rwa [c2, Subgroup.mem_bot] at hmem
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
  have hYcomm : ∀ a ∈ dsOmega1 (centerOf (dsQ L2 L1 S)), ∀ b ∈ dsOmega1 (centerOf (dsQ L2 L1 S)),
      a * b = b * a :=
    fun a ha b hb => congrArg Subtype.val (isMulCommutative_iff.mp hYab.1 ⟨a, ha⟩ ⟨b, hb⟩)
  have hbotN : Subgroup.normalizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
    Subgroup.normalizer_eq_top (⊥ : Subgroup G)
  have hPK : L2 ⊔ bigB L2 L1 S ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [hbotN]; exact le_top
  have hcomm1 : ∀ l ∈ L2, ∀ y ∈ dsOmega1 (centerOf (dsQ L2 L1 S)), l * y = y * l := by
    by_contra hcon
    push Not at hcon
    obtain ⟨l, hl, y, hy, hne⟩ := hcon
    have hnt : ∃ l ∈ L2, ∃ e ∈ dsOmega1 (centerOf (dsQ L2 L1 S)), ⁅l, e⁆ ∉ (⊥ : Subgroup G) :=
      ⟨l, hl, y, hy, fun h1 => hne (commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp h1))⟩
    have hsecY : IsElemSec (⊥ : Subgroup G) (dsOmega1 (centerOf (dsQ L2 L1 S))) := by
      unfold IsElemSec
      refine ⟨bot_le, Subgroup.commutator_le.mpr fun a ha b hb => ?_, fun e he => ?_⟩
      · exact Subgroup.mem_bot.mpr (commutatorElement_eq_one_iff_mul_comm.mpr (hYcomm a ha b hb))
      · exact Subgroup.mem_bot.mpr (hYab.2 e he)
    have hcardY : (⊥ : Subgroup G).relIndex (dsOmega1 (centerOf (dsQ L2 L1 S))) ≤ 16 := by
      rw [Subgroup.relIndex_bot_left]; exact hYcard
    have hcoreY : ∀ q ∈ pCoreOf 2 (L2 ⊔ bigB L2 L1 S), ∀ e ∈ dsOmega1 (centerOf (dsQ L2 L1 S)),
        ⁅q, e⁆ ∈ (⊥ : Subgroup G) := by
      intro q hq e he
      refine Subgroup.mem_bot.mpr (commutatorElement_eq_one_iff_mul_comm.mpr ?_)
      exact (dsa2_mem_centerOf.mp (dsa2_dsOmega1_le (centerOf (dsQ L2 L1 S)) he)).2 q hq
    have hA : A5Chief (L2 ⊔ bigB L2 L1 S) L2 (dsOmega1 (centerOf (dsQ L2 L1 S))) ⊥ :=
      faithful_a5 hA5.le hA5.norm (hYQ.trans hQP) hPY hPK hsecY hcardY hA5.quot hcoreY hnt
    have hX := hA.irred (dsOmega1 (centerOf (dsQ L2 L1 S)) ⊓ Subgroup.centralizer (L2 : Set G))
      bot_le inf_le_left (dsa2_le_normalizer_centralizer hA5.norm hPY)
    rcases hX with hX | hX
    ·
      have hZX : dsZ S ≤ dsOmega1 (centerOf (dsQ L2 L1 S)) ⊓ Subgroup.centralizer (L2 : Set G) :=
        fun z hz => Subgroup.mem_inf.mpr
          ⟨hZY hz, Subgroup.mem_centralizer_iff.mpr fun l hl => hZc z hz l hl⟩
      rw [hX] at hZX
      exact hZne (le_bot_iff.mp hZX)
    ·
      have hyC : y ∈ dsOmega1 (centerOf (dsQ L2 L1 S)) ⊓ Subgroup.centralizer (L2 : Set G) := by
        rw [hX]; exact hy
      exact hne (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hyC).2 l hl)
  have hYZ : dsOmega1 (centerOf (dsQ L2 L1 S)) ≤ dsZ S := by
    have hSC : S ≤ Subgroup.centralizer ((dsOmega1 (centerOf (dsQ L2 L1 S)) : Subgroup G) : Set G) := by
      calc S = (S ⊓ L2) ⊔ dsQ L2 L1 S := hS2
        _ ≤ Subgroup.centralizer ((dsOmega1 (centerOf (dsQ L2 L1 S)) : Subgroup G) : Set G) := by
          refine sup_le (fun s hs => Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
            (fun q hq => Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
          · exact (hcomm1 s (Subgroup.mem_inf.mp hs).2 y hy).symm
          · exact ((dsa2_mem_centerOf.mp (dsa2_dsOmega1_le (centerOf (dsQ L2 L1 S)) hy)).2 q hq).symm
    intro y hy
    refine dsa2_mem_dsOmega1 (X := centerOf S)
      (dsa2_mem_centerOf.mpr ⟨hQS (hYQ hy), fun s hs => ?_⟩) (hYab.2 y hy)
    exact (Subgroup.mem_centralizer_iff.mp (hSC hs) y hy).symm
  have hYeq : dsOmega1 (centerOf (dsQ L2 L1 S)) = dsZ S := le_antisymm hYZ hZY
  have hZΦ : dsZ S ≤ dsFrattini (dsQ L2 L1 S) := by
    have hPΦ : L2 ⊔ bigB L2 L1 S ≤
        Subgroup.normalizer ((dsFrattini (dsQ L2 L1 S) : Subgroup G) : Set G) := hFC.norm_K
    have hPQ : L2 ⊔ bigB L2 L1 S ≤ Subgroup.normalizer ((dsQ L2 L1 S : Subgroup G) : Set G) :=
      hFC.norm_E
    have hirr := hFC.irred
      (dsQ L2 L1 S ⊓ dsCentMod (L2 ⊔ bigB L2 L1 S) L2 (dsFrattini (dsQ L2 L1 S)))
      (dsa2_le_centMod hA5.le hA5.norm hPΦ (hΦQ.trans hQP) hΦQ) inf_le_left
      (dsa2_le_normalizer_centMod hA5.norm hPQ hPΦ)
    rcases hirr with hX | hX
    · intro z hz
      rw [← hX]
      refine Subgroup.mem_inf.mpr ⟨hZQ hz, dsa2_mem_dsCentMod.mpr
        ⟨hQP (hZQ hz), hPΦ (hQP (hZQ hz)), fun l hl => ?_⟩⟩
      rw [commutatorElement_eq_one_iff_mul_comm.mpr (hZc z hz l hl).symm]
      exact Subgroup.one_mem _
    · exfalso
      obtain ⟨l, hl, e, he, hne⟩ := hFC.nontriv
      have heX : e ∈ dsQ L2 L1 S ⊓ dsCentMod (L2 ⊔ bigB L2 L1 S) L2 (dsFrattini (dsQ L2 L1 S)) := by
        rw [hX]; exact he
      have h1 := (dsa2_mem_dsCentMod.mp (Subgroup.mem_inf.mp heX).2).2.2 l hl
      have h2 := Subgroup.inv_mem _ h1
      rw [commutatorElement_inv] at h2
      exact hne h2
  exact ⟨hYeq, hZΦ⟩

end CFSG.GH74.QTGen4.DSGen4
