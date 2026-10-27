module

public import CFSG.ClassicalInvolution.Q3.Q3CHS2Gold
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FStarBasic
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FStar178

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.Q3T.MFS

theorem eq_bot_of_stronglyClosed_of_sixteen {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) {z a b : G} (hz : orderOf z = 2)
    (ha : a ∈ Subgroup.centralizer ({z} : Set G)) (hb : b ∈ Subgroup.centralizer ({z} : Set G))
    (ha2 : orderOf a = 2) (hb2 : orderOf b = 2) (hab : a * b ≠ b * a)
    {P : Subgroup G} (hP2 : IsPGroup 2 P) (hP16 : 16 ≤ Nat.card P) (T : Sylow 2 G)
    {A : Subgroup G} (hAT : A ≤ (T : Subgroup G)) (hAab : IsMulCommutative A)
    (hcl : ∀ a ∈ A, ∀ g : G, g⁻¹ * a * g ∈ (T : Subgroup G) → g⁻¹ * a * g ∈ A) : A = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hA1
  have hS := Hat2A7.goldschmidtSimpleType_of_milestone
    CFSG.Milestones.cl_lit_goldschmidt_strongly_closed_abelian hnab T hA1 hAT hAab hcl
  have hbender : fusionIsBenderGroup G → False := fun hB =>
    hab (Q3CH.commute_of_isBenderGroup
      (Disconnected.AschTight.isBenderGroup_of_fusionIsBenderGroup' hB) hz ha hb ha2 hb2)
  have hsmall : ∀ a j : ℕ, a ≤ 3 → Odd j → Nat.card G = 2 ^ a * j → False := by
    intro a j ha hj hG
    obtain ⟨T', hPT'⟩ := hP2.exists_le_sylow
    have hT'le : Nat.card (T' : Subgroup G) ≤ 8 :=
      (Disconnected.AschTight.card_le_of_isPGroup_of_card_eq T'.isPGroup' hj hG).trans
        (le_of_le_of_eq (Nat.pow_le_pow_right (by norm_num) ha) (by norm_num))
    have := Subgroup.card_le_of_le hPT'
    omega
  rcases hS with ⟨f, hf, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ |
    ⟨p, f, hp, hodd, hf0, -, hmod, ⟨e⟩⟩ | ⟨m, -, hcard⟩ | ⟨⟨e⟩⟩
  · exact hbender (Or.inl ⟨f, by omega, ⟨e⟩⟩)
  · exact hbender (Or.inr (Or.inr ⟨n, hn, ⟨e⟩⟩))
  · exact hbender (Or.inr (Or.inl ⟨f, hf, ⟨e⟩⟩))
  · have hf0' : f ≠ 0 := by omega
    have hK : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf0'
    have hodd' : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField p f)) :=
      ⟨p, f, hp.out, hodd, hf0, hK⟩
    have hc := CFSG.GorensteinWalter.psl2_card_formula (GaloisField p f) hodd'
    rw [hK] at hc
    obtain ⟨j, hj, hj4⟩ := Hat2A7.psl2_card_eq_four_mul_odd hmod
    exact hsmall 2 j (by norm_num) hj (by
      rw [Nat.card_congr e.toEquiv]
      exact hc.trans (hj4.trans (by norm_num)))
  · obtain ⟨j, hj, hj8⟩ := Hat2A7.ordRee_eq_eight_mul_odd m
    exact hsmall 3 j le_rfl hj (by rw [hcard, hj8]; norm_num)
  · exact hsmall 3 21945 le_rfl ⟨10972, by norm_num⟩
      (by rw [← Hat2A7.card_goldschmidtJ1_eq, Nat.card_congr e.toEquiv])

variable {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup (genFittingFStar Y)]

theorem inf_fstar_eq_bot_of_stronglyClosed (hnab : ∃ a b : genFittingFStar Y, a * b ≠ b * a)
    {z a b : Y} (hzL : z ∈ genFittingFStar Y) (haL : a ∈ genFittingFStar Y)
    (hbL : b ∈ genFittingFStar Y) (hz : orderOf z = 2)
    (ha : a ∈ Subgroup.centralizer ({z} : Set Y)) (hb : b ∈ Subgroup.centralizer ({z} : Set Y))
    (ha2 : orderOf a = 2) (hb2 : orderOf b = 2) (hab : a * b ≠ b * a)
    {P : Subgroup Y} (hPL : P ≤ genFittingFStar Y) (hP2 : IsPGroup 2 P) (hP16 : 16 ≤ Nat.card P)
    (T : Sylow 2 Y) {A : Subgroup Y} (hAT : A ≤ (T : Subgroup Y)) (hAab : IsMulCommutative A)
    (hcl : ∀ a ∈ A, ∀ g : Y, g⁻¹ * a * g ∈ (T : Subgroup Y) → g⁻¹ * a * g ∈ A) :
    A ⊓ genFittingFStar Y = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := genFittingFStar Y
  haveI : L.Normal := fstar_normal
  obtain ⟨TL, hTL⟩ := Glauberman.sylow_inf_normal T (N := L)
  have hcen : ∀ {x : Y} (hx : x ∈ L), x ∈ Subgroup.centralizer ({z} : Set Y) →
      (⟨x, hx⟩ : L) ∈ Subgroup.centralizer ({⟨z, hzL⟩} : Set L) := fun {x} hx hxz =>
    Subgroup.mem_centralizer_iff.2 fun w hw => by
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.1 hxz) z rfl)
  have hord : ∀ {x : Y} (hx : x ∈ L), orderOf (⟨x, hx⟩ : L) = orderOf x := fun {x} hx =>
    (Subgroup.orderOf_coe (⟨x, hx⟩ : L)).symm
  have hAabL : IsMulCommutative ((A ⊓ L).subgroupOf L) := ⟨⟨fun x y => by
    have := congrArg Subtype.val (hAab.is_comm.comm ⟨x.1.1, (Subgroup.mem_inf.1 x.2).1⟩
      ⟨y.1.1, (Subgroup.mem_inf.1 y.2).1⟩)
    exact Subtype.ext (Subtype.ext (by simpa using this))⟩⟩
  have hA := eq_bot_of_stronglyClosed_of_sixteen (G := L) hnab (z := ⟨z, hzL⟩)
    (a := ⟨a, haL⟩) (b := ⟨b, hbL⟩) (by rw [hord]; exact hz) (hcen _ ha) (hcen _ hb)
    (by rw [hord]; exact ha2) (by rw [hord]; exact hb2)
    (fun h => hab (congrArg Subtype.val h)) (P := P.subgroupOf L)
    (hP2.comap_of_injective L.subtype Subtype.val_injective)
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPL).toEquiv]; exact hP16)
    TL (A := (A ⊓ L).subgroupOf L)
    (fun x hx => by
      rw [hTL, Subgroup.mem_subgroupOf]
      rw [Subgroup.mem_subgroupOf] at hx
      exact ⟨hAT (Subgroup.mem_inf.1 hx).1, (Subgroup.mem_inf.1 hx).2⟩)
    hAabL
    (fun x hx g hg => by
      rw [hTL, Subgroup.mem_subgroupOf] at hg
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      refine ⟨?_, (g⁻¹ * x * g).2⟩
      simpa using hcl _ (Subgroup.mem_inf.1 hx).1 g (by simpa using (Subgroup.mem_inf.1 hg).1))
  exact (Subgroup.subgroupOf_eq_bot.1 hA).eq_bot_of_le inf_le_right

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FStar178

