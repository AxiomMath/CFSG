module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.Sol76SigFourConn
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.Sol76.Sig.GSYard02

open CFSG Subgroup

private theorem commute_of_isKleinFour_gsy {X : Type} [Group X] {E : Subgroup X}
    (hE : IsKleinFour E) {g h : X} (hg : g ∈ E) (hh : h ∈ E) : Commute g h := by
  have hinv : ∀ x ∈ E, x⁻¹ = x := fun x hx => by
    rw [inv_eq_iff_mul_eq_one, ← sq]
    exact FooteLit.sq_eq_one_of_isKleinFour hE hx
  have hgh : g * h ∈ E := E.mul_mem hg hh
  show g * h = h * g
  calc g * h = (g * h)⁻¹ := (hinv _ hgh).symm
    _ = h⁻¹ * g⁻¹ := mul_inv_rev g h
    _ = h * g := by rw [hinv g hg, hinv h hh]

private theorem exists_mem_ne_ne_gsy {X : Type} [Group X] {E : Subgroup X} (h4 : Nat.card E = 4)
    (y : X) : ∃ x ∈ E, x ≠ 1 ∧ x ≠ y := by
  by_contra hc
  push_neg at hc
  have hsub : (E : Set X) ⊆ {1, y} := fun x hx => by
    by_cases h1 : x = 1
    · exact Or.inl h1
    · exact Or.inr (hc x hx h1)
  have hle : Nat.card E ≤ 2 := by
    have e : Nat.card E = (E : Set X).ncard := Nat.card_coe_set_eq (E : Set X)
    rw [e]
    calc (E : Set X).ncard ≤ ({1, y} : Set X).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ ({y} : Set X).ncard + 1 := Set.ncard_insert_le 1 {y}
      _ = 2 := by rw [Set.ncard_singleton]
  omega

private theorem mem_kf_gsy {X : Type} [Group X] {a b : X} {ha : a * a = 1} {hb : b * b = 1}
    {hab : Commute a b} {g : X} :
    g ∈ GorensteinWalter.kleinFourOfCommutingInvolutions a b ha hb hab ↔
      g = a * b ∨ g = a ∨ g = b ∨ g = 1 :=
  Iff.rfl

private theorem commute_mem_kf_gsy {X : Type} [Group X] {a b g : X} {ha : a * a = 1}
    {hb : b * b = 1} {hab : Commute a b} (hga : Commute g a) (hgb : Commute g b) {k : X}
    (hk : k ∈ GorensteinWalter.kleinFourOfCommutingInvolutions a b ha hb hab) : Commute g k := by
  rcases mem_kf_gsy.mp hk with h | h | h | h
  · rw [h]
    exact hga.mul_right hgb
  · rw [h]
    exact hga
  · rw [h]
    exact hgb
  · rw [h]
    exact Commute.one_right g

private theorem commute_kf_kf_gsy {X : Type} [Group X] {a b c d : X} {ha : a * a = 1}
    {hb : b * b = 1} {hab : Commute a b} {hc : c * c = 1} {hd : d * d = 1} {hcd : Commute c d}
    (hac : Commute a c) (had : Commute a d) (hbc : Commute b c) (hbd : Commute b d) :
    ∀ g ∈ GorensteinWalter.kleinFourOfCommutingInvolutions a b ha hb hab,
      ∀ k ∈ GorensteinWalter.kleinFourOfCommutingInvolutions c d hc hd hcd, Commute g k := by
  intro g hg k hk
  have hgc : Commute g c := (commute_mem_kf_gsy hac.symm hbc.symm hg).symm
  have hgd : Commute g d := (commute_mem_kf_gsy had.symm hbd.symm hg).symm
  exact commute_mem_kf_gsy hgc hgd hk

private theorem commFourAdj_of_forall_commute_gsy {X : Type} [Group X] {B C : Subgroup X}
    (hB : IsKleinFour B) (hC : IsKleinFour C) (h : ∀ g ∈ B, ∀ k ∈ C, Commute g k) :
    CommFourAdj X B C := by
  refine ⟨hB, hC, ?_⟩
  intro g hg
  rw [mem_centralizer_iff]
  intro k hk
  exact (h g hg k hk).symm.eq

theorem reflTransGen_commFourAdj_of_wreath {X : Type} [Group X] [Finite X] {S A B : Subgroup X}
    {τ z₁ c : X} (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hAB1 : A ⊓ B = ⊥)
    (hτ : τ * τ = 1) (hτA : ∀ a ∈ A, τ * a * τ ∈ B) (hτB : ∀ b ∈ B, τ * b * τ ∈ A)
    (hS : ∀ s ∈ S, ∃ a ∈ A, ∃ b ∈ B, s = a * b ∨ s = a * b * τ)
    (hAS : A ≤ S) (hBS : B ≤ S) (hτS : τ ∈ S)
    (hz₁ : z₁ ∈ A) (hz₁2 : z₁ * z₁ = 1) (hz₁1 : z₁ ≠ 1) (hz₁c : ∀ a ∈ A, a * z₁ = z₁ * a)
    (hc : c ∈ A) (hc2 : c * c = 1) (hcz : c ≠ z₁) (hc1 : c ≠ 1)
    {E F : Subgroup X} (hE : IsKleinFour E) (hES : E ≤ S) (hF : IsKleinFour F) (hFS : F ≤ S) :
    Relation.ReflTransGen (CommFourAdj X) E F := by
  have hABtriv : ∀ g ∈ A, g ∈ B → g = 1 := fun g hgA hgB => by
    have hmem : g ∈ A ⊓ B := Subgroup.mem_inf.mpr ⟨hgA, hgB⟩
    rw [hAB1] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hABuniq : ∀ {a₁ a₂ b₁ b₂ : X}, a₁ ∈ A → a₂ ∈ A → b₁ ∈ B → b₂ ∈ B →
      a₁ * b₁ = a₂ * b₂ → a₁ = a₂ := by
    intro a₁ a₂ b₁ b₂ h₁ h₂ k₁ k₂ h
    have hmemA : a₂⁻¹ * a₁ ∈ A := A.mul_mem (A.inv_mem h₂) h₁
    have heq : a₂⁻¹ * a₁ = b₂ * b₁⁻¹ := by
      calc a₂⁻¹ * a₁ = a₂⁻¹ * (a₁ * b₁) * b₁⁻¹ := by group
        _ = a₂⁻¹ * (a₂ * b₂) * b₁⁻¹ := by rw [h]
        _ = b₂ * b₁⁻¹ := by group
    have hmemB : a₂⁻¹ * a₁ ∈ B := by
      rw [heq]
      exact B.mul_mem k₂ (B.inv_mem k₁)
    exact (inv_mul_eq_one.mp (hABtriv _ hmemA hmemB)).symm
  obtain ⟨w, hw⟩ : ∃ w : X, w = τ * z₁ * τ := ⟨_, rfl⟩
  have hwB : w ∈ B := by
    rw [hw]
    exact hτA z₁ hz₁
  have hww : w * w = 1 := by
    rw [hw]
    calc τ * z₁ * τ * (τ * z₁ * τ) = τ * z₁ * (τ * τ) * z₁ * τ := by group
      _ = τ * (z₁ * z₁) * τ := by rw [hτ]; group
      _ = τ * τ := by rw [hz₁2]; group
      _ = 1 := hτ
  have hτwτ : τ * w * τ = z₁ := by
    rw [hw]
    calc τ * (τ * z₁ * τ) * τ = (τ * τ) * z₁ * (τ * τ) := by group
      _ = z₁ := by rw [hτ]; group
  have hz₁w : z₁ * w = w * z₁ := hAB z₁ hz₁ w hwB
  have hwcomm : ∀ b ∈ B, w * b = b * w := by
    intro b hb
    obtain ⟨a', ha', hba'⟩ : ∃ a' ∈ A, b = τ * a' * τ :=
      ⟨τ * b * τ, hτB b hb, by
        calc b = (τ * τ) * b * (τ * τ) := by rw [hτ, one_mul, mul_one]
          _ = τ * (τ * b * τ) * τ := by group⟩
    subst hba'
    rw [hw]
    calc τ * z₁ * τ * (τ * a' * τ) = τ * z₁ * (τ * τ) * a' * τ := by group
      _ = τ * (z₁ * a') * τ := by rw [hτ]; group
      _ = τ * (a' * z₁) * τ := by rw [hz₁c a' ha']
      _ = τ * a' * (τ * τ) * z₁ * τ := by rw [hτ]; group
      _ = τ * a' * τ * (τ * z₁ * τ) := by group
  obtain ⟨z, hz⟩ : ∃ z : X, z = z₁ * w := ⟨_, rfl⟩
  have hzz : z * z = 1 := by
    rw [hz]
    calc z₁ * w * (z₁ * w) = z₁ * (w * z₁) * w := by group
      _ = z₁ * (z₁ * w) * w := by rw [← hz₁w]
      _ = (z₁ * z₁) * (w * w) := by group
      _ = 1 := by rw [hz₁2, hww, one_mul]
  have hz1 : z ≠ 1 := by
    intro h
    have h' : z₁ * w = 1 := by
      rw [← hz]
      exact h
    have hz₁B : z₁ = w := by
      calc z₁ = z₁ * w * w := by rw [mul_assoc, hww, mul_one]
        _ = w := by rw [h', one_mul]
    exact hz₁1 (hABtriv z₁ hz₁ (by rw [hz₁B]; exact hwB))
  have hz₁z : Commute z₁ z := by
    show z₁ * z = z * z₁
    rw [hz]
    calc z₁ * (z₁ * w) = z₁ * (w * z₁) := by rw [← hz₁w]
      _ = z₁ * w * z₁ := by group
  have hz₁z' : z₁ ≠ z := by
    intro h
    have hw1 : w = 1 := by
      apply mul_left_cancel (a := z₁)
      rw [mul_one, ← hz, h]
    have h1 := hτwτ
    rw [hw1, mul_one, hτ] at h1
    exact hz₁1 h1.symm
  have hτz : τ * z * τ = z := by
    rw [hz]
    calc τ * (z₁ * w) * τ = τ * z₁ * (τ * τ) * w * τ := by rw [hτ]; group
      _ = (τ * z₁ * τ) * (τ * w * τ) := by group
      _ = w * z₁ := by rw [hτwτ, ← hw]
      _ = z₁ * w := hz₁w.symm
  have hτzc : τ * z = z * τ := by
    calc τ * z = τ * z * τ * τ := by rw [mul_assoc (τ * z) τ τ, hτ, mul_one]
      _ = z * τ := by rw [hτz]
  have hAz : ∀ a ∈ A, Commute a z := by
    intro a ha
    rw [hz]
    exact (show Commute a z₁ from hz₁c a ha).mul_right (show Commute a w from hAB a ha w hwB)
  have hBz : ∀ b ∈ B, Commute b z := by
    intro b hb
    rw [hz]
    exact (show Commute b z₁ from (hAB z₁ hz₁ b hb).symm).mul_right
      (show Commute b w from (hwcomm b hb).symm)
  have hτz' : Commute τ z := hτzc
  have hzcen : ∀ s ∈ S, Commute s z := by
    intro s hs
    obtain ⟨a, ha, b, hb, rfl | rfl⟩ := hS s hs
    · exact (hAz a ha).mul_left (hBz b hb)
    · exact ((hAz a ha).mul_left (hBz b hb)).mul_left hτz'
  obtain ⟨V, hVdef⟩ : ∃ V : Subgroup X,
      V = GorensteinWalter.kleinFourOfCommutingInvolutions z₁ z hz₁2 hzz hz₁z := ⟨_, rfl⟩
  have hVK : IsKleinFour V := by
    rw [hVdef]
    exact GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions z₁ z hz₁2 hzz hz₁1 hz1
      hz₁z' hz₁z
  have hABclaim : ∀ (y : X) (hyS : y ∈ S) (hy : y * y = 1) (hy1 : y ≠ 1) (hyz : y ≠ z)
      (a' : X) (ha' : a' ∈ A) (b' : X) (hb' : b' ∈ B), y = a' * b' →
      Relation.ReflTransGen (CommFourAdj X)
        (GorensteinWalter.kleinFourOfCommutingInvolutions y z hy hzz (hzcen y hyS)) V := by
    intro y hyS hy hy1 hyz a' ha' b' hb' hyeq
    have hyz₁ : Commute y z₁ := by
      rw [hyeq]
      exact (show Commute a' z₁ from hz₁c a' ha').mul_left
        (show Commute b' z₁ from (hAB z₁ hz₁ b' hb').symm)
    have hK : IsKleinFour
        (GorensteinWalter.kleinFourOfCommutingInvolutions y z hy hzz (hzcen y hyS)) :=
      GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions y z hy hzz hy1 hz1 hyz
        (hzcen y hyS)
    have hadj : CommFourAdj X
        (GorensteinWalter.kleinFourOfCommutingInvolutions y z hy hzz (hzcen y hyS)) V := by
      rw [hVdef]
      exact commFourAdj_of_forall_commute_gsy hK
        (GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions z₁ z hz₁2 hzz hz₁1 hz1
          hz₁z' hz₁z)
        (commute_kf_kf_gsy hyz₁ (hzcen y hyS) hz₁z.symm (Commute.refl z))
    exact Relation.ReflTransGen.single hadj
  have hclaimB : ∀ (x : X) (hxS : x ∈ S) (hx : x * x = 1) (hx1 : x ≠ 1) (hxz : x ≠ z),
      Relation.ReflTransGen (CommFourAdj X)
        (GorensteinWalter.kleinFourOfCommutingInvolutions x z hx hzz (hzcen x hxS)) V := by
    intro x hxS hx hx1 hxz
    obtain ⟨a, ha, b, hb, hxab | hxab⟩ := hS x hxS
    · exact hABclaim x hxS hx hx1 hxz a ha b hb hxab
    · have hτb : τ * b * τ ∈ A := hτB b hb
      have ha' : τ * a * τ ∈ B := hτA a ha
      have hPQ : a * (τ * b * τ) * (b * (τ * a * τ)) = 1 := by
        have hc1' : τ * b * τ * b = b * (τ * b * τ) := hAB (τ * b * τ) hτb b hb
        have hc2' : τ * b * τ * (τ * a * τ) = τ * a * τ * (τ * b * τ) :=
          hAB (τ * b * τ) hτb (τ * a * τ) ha'
        calc a * (τ * b * τ) * (b * (τ * a * τ)) = a * ((τ * b * τ) * b) * (τ * a * τ) := by group
          _ = a * (b * (τ * b * τ)) * (τ * a * τ) := by rw [hc1']
          _ = a * b * ((τ * b * τ) * (τ * a * τ)) := by group
          _ = a * b * ((τ * a * τ) * (τ * b * τ)) := by rw [hc2']
          _ = a * b * τ * a * (τ * τ) * b * τ := by group
          _ = a * b * τ * a * b * τ := by rw [hτ]; group
          _ = x * x := by rw [hxab]; group
          _ = 1 := hx
      have hPB : a * (τ * b * τ) ∈ B := by
        rw [eq_inv_of_mul_eq_one_left hPQ]
        exact B.inv_mem (B.mul_mem hb ha')
      have hP1 : a * (τ * b * τ) = 1 := hABtriv _ (A.mul_mem ha hτb) hPB
      have hτb' : τ * b * τ = a⁻¹ := eq_inv_of_mul_eq_one_right hP1
      have hbeq : b = τ * a⁻¹ * τ := by
        calc b = (τ * τ) * b * (τ * τ) := by rw [hτ, one_mul, mul_one]
          _ = τ * (τ * b * τ) * τ := by group
          _ = τ * a⁻¹ * τ := by rw [hτb']
      have hxeq : x = a * τ * a⁻¹ := by
        rw [hxab, hbeq]
        calc a * (τ * a⁻¹ * τ) * τ = a * τ * a⁻¹ * (τ * τ) := by group
          _ = a * τ * a⁻¹ := by rw [hτ, mul_one]
      obtain ⟨u, hudef⟩ : ∃ u : X, u = c * (τ * c * τ) := ⟨_, rfl⟩
      have hcw : c * (τ * c * τ) = τ * c * τ * c := hAB c hc (τ * c * τ) (hτA c hc)
      have hτu : τ * u * τ = u := by
        rw [hudef]
        calc τ * (c * (τ * c * τ)) * τ = τ * c * τ * c * (τ * τ) := by group
          _ = τ * c * τ * c := by rw [hτ, mul_one]
          _ = c * (τ * c * τ) := hcw.symm
      have hu_comm : τ * u = u * τ := by
        calc τ * u = τ * u * τ * τ := by rw [mul_assoc (τ * u) τ τ, hτ, mul_one]
          _ = u * τ := by rw [hτu]
      have hu2 : u * u = 1 := by
        have hwc2 : τ * c * τ * (τ * c * τ) = 1 := by
          calc τ * c * τ * (τ * c * τ) = τ * c * (τ * τ) * c * τ := by group
            _ = τ * c * c * τ := by rw [hτ, mul_one]
            _ = τ * (c * c) * τ := by group
            _ = τ * τ := by rw [hc2, mul_one]
            _ = 1 := hτ
        rw [hudef]
        calc c * (τ * c * τ) * (c * (τ * c * τ))
            = c * ((τ * c * τ) * c) * (τ * c * τ) := by group
          _ = c * (c * (τ * c * τ)) * (τ * c * τ) := by
              rw [← hAB c hc (τ * c * τ) (hτA c hc)]
          _ = (c * c) * ((τ * c * τ) * (τ * c * τ)) := by group
          _ = 1 := by rw [hc2, hwc2, one_mul]
      have ha'' : a * c * a⁻¹ ∈ A := A.mul_mem (A.mul_mem ha hc) (A.inv_mem ha)
      have hb'' : τ * c * τ ∈ B := hτA c hc
      obtain ⟨y, hydef⟩ : ∃ y : X, y = a * u * a⁻¹ := ⟨_, rfl⟩
      have hyAB : y = (a * c * a⁻¹) * (τ * c * τ) := by
        rw [hydef, hudef]
        have hcomm_aw : a * (τ * c * τ) = (τ * c * τ) * a := hAB a ha (τ * c * τ) hb''
        calc a * (c * (τ * c * τ)) * a⁻¹ = (a * c) * (τ * c * τ) * a⁻¹ := by group
          _ = (a * c * a⁻¹) * (a * (τ * c * τ) * a⁻¹) := by group
          _ = (a * c * a⁻¹) * ((τ * c * τ) * a * a⁻¹) := by rw [hcomm_aw]
          _ = (a * c * a⁻¹) * (τ * c * τ) := by group
      have hyS : y ∈ S := by
        rw [hyAB]
        exact S.mul_mem (hAS ha'') (hBS hb'')
      have hy2 : y * y = 1 := by
        rw [hydef]
        calc a * u * a⁻¹ * (a * u * a⁻¹) = a * (u * u) * a⁻¹ := by group
          _ = 1 := by rw [hu2]; group
      have hy1 : y ≠ 1 := by
        intro h
        have h' : (a * c * a⁻¹) * (τ * c * τ) = 1 * 1 := by rw [← hyAB, h, one_mul]
        have hna : a * c * a⁻¹ = 1 := hABuniq ha'' A.one_mem hb'' B.one_mem h'
        apply hc1
        calc c = a⁻¹ * (a * c * a⁻¹) * a := by group
          _ = 1 := by rw [hna]; group
      have hyz : y ≠ z := by
        intro h
        have h' : (a * c * a⁻¹) * (τ * c * τ) = z₁ * w := by rw [← hyAB, h, hz]
        have hna : a * c * a⁻¹ = z₁ := hABuniq ha'' hz₁ hb'' hwB h'
        apply hcz
        calc c = a⁻¹ * (a * c * a⁻¹) * a := by group
          _ = a⁻¹ * z₁ * a := by rw [hna]
          _ = a⁻¹ * (z₁ * a) := by rw [mul_assoc]
          _ = a⁻¹ * (a * z₁) := by rw [hz₁c a ha]
          _ = z₁ := by group
      have hxy : Commute x y := by
        show x * y = y * x
        rw [hxeq, hydef]
        calc a * τ * a⁻¹ * (a * u * a⁻¹) = a * (τ * u) * a⁻¹ := by group
          _ = a * (u * τ) * a⁻¹ := by rw [hu_comm]
          _ = a * u * a⁻¹ * (a * τ * a⁻¹) := by group
      have hKx : IsKleinFour
          (GorensteinWalter.kleinFourOfCommutingInvolutions x z hx hzz (hzcen x hxS)) :=
        GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions x z hx hzz hx1 hz1 hxz
          (hzcen x hxS)
      have hKy : IsKleinFour
          (GorensteinWalter.kleinFourOfCommutingInvolutions y z hy2 hzz (hzcen y hyS)) :=
        GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions y z hy2 hzz hy1 hz1 hyz
          (hzcen y hyS)
      have hadj : CommFourAdj X
          (GorensteinWalter.kleinFourOfCommutingInvolutions x z hx hzz (hzcen x hxS))
          (GorensteinWalter.kleinFourOfCommutingInvolutions y z hy2 hzz (hzcen y hyS)) :=
        commFourAdj_of_forall_commute_gsy hKx hKy
          (commute_kf_kf_gsy hxy (hzcen x hxS) (hzcen y hyS).symm (Commute.refl z))
      exact (Relation.ReflTransGen.single hadj).trans
        (hABclaim y hyS hy2 hy1 hyz (a * c * a⁻¹) ha'' (τ * c * τ) hb'' hyAB)
  have hjoin : ∀ D : Subgroup X, IsKleinFour D → D ≤ S →
      Relation.ReflTransGen (CommFourAdj X) D V := by
    intro D hD hDS
    obtain ⟨x, hxD, hx1, hxz⟩ := exists_mem_ne_ne_gsy hD.card_four z
    have hxS : x ∈ S := hDS hxD
    have hx : x * x = 1 := by
      rw [← sq]
      exact FooteLit.sq_eq_one_of_isKleinFour hD hxD
    have hKx : IsKleinFour
        (GorensteinWalter.kleinFourOfCommutingInvolutions x z hx hzz (hzcen x hxS)) :=
      GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions x z hx hzz hx1 hz1 hxz
        (hzcen x hxS)
    have hadj : CommFourAdj X D
        (GorensteinWalter.kleinFourOfCommutingInvolutions x z hx hzz (hzcen x hxS)) :=
      commFourAdj_of_forall_commute_gsy hD hKx (fun g hg k hk =>
        commute_mem_kf_gsy (commute_of_isKleinFour_gsy hD hg hxD) (hzcen g (hDS hg)) hk)
    exact (Relation.ReflTransGen.single hadj).trans (hclaimB x hxS hx hx1 hxz)
  exact (hjoin E hE hES).trans (reflTransGen_commFourAdj_symm (hjoin F hF hFS))

end CFSG.ComponentClassification.Sol76.Sig.GSYard02
