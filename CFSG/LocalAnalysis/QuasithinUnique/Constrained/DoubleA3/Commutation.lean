module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.BlockRank1
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCCases

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup
open scoped commutatorElement

section Generic

variable {G : Type} [Group G]

theorem le_centralizer_iff_conj {A B : Subgroup G} (g : G) :
    A ≤ centralizer (B : Set G) ↔
      conjSubgroup A g ≤ centralizer ((conjSubgroup B g : Subgroup G) : Set G) := by
  rw [← C5.conjSubgroup_centralizer, C5.conjSubgroup_le_iff]

theorem not_conj_inv_le_centralizer {U : Subgroup G} {x : G}
    (h : ¬ conjSubgroup U x ≤ centralizer (U : Set G)) :
    ¬ conjSubgroup U x⁻¹ ≤ centralizer (U : Set G) := by
  intro hle
  apply h
  have h1 := (le_centralizer_iff_conj x).mp hle
  rw [C5.conjSubgroup_inv_conjSubgroup] at h1
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  exact (Subgroup.mem_centralizer_iff.mp (h1 hu) a ha).symm

theorem commutator_sup_sup_eq_bot {A B C D : Subgroup G}
    (hAC : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a) (hAD : ∀ a ∈ A, ∀ d ∈ D, a * d = d * a)
    (hBC : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b) (hBD : ∀ b ∈ B, ∀ d ∈ D, b * d = d * b) :
    ⁅A ⊔ B, C ⊔ D⁆ = ⊥ := by
  have key : ∀ a : G, (∀ c ∈ C, a * c = c * a) → (∀ d ∈ D, a * d = d * a) →
      ∀ y ∈ C ⊔ D, a * y = y * a := by
    intro a hC hD y hy
    have : C ⊔ D ≤ centralizer ({a} : Set G) := sup_le
      (fun c hc => Subgroup.mem_centralizer_singleton_iff.mpr (hC c hc).symm)
      (fun d hd => Subgroup.mem_centralizer_singleton_iff.mpr (hD d hd).symm)
    exact (Subgroup.mem_centralizer_singleton_iff.mp (this hy)).symm
  have key2 : ∀ y ∈ C ⊔ D, ∀ x ∈ A ⊔ B, x * y = y * x := by
    intro y hy x hx
    have : A ⊔ B ≤ centralizer ({y} : Set G) := sup_le
      (fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr (key a (hAC a ha) (hAD a ha) y hy))
      (fun b hb => Subgroup.mem_centralizer_singleton_iff.mpr (key b (hBC b hb) (hBD b hb) y hy))
    exact Subgroup.mem_centralizer_singleton_iff.mp (this hx)
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (key2 y hy x hx).symm

end Generic

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {s : G}

theorem mem_pCoreOf_of_centralizes (hcfg : A3A3 T M H S L s)
    (hU0 : blockU0 S L = pCoreOf 2 (conjJoin S L))
    (hQ : pCoreOf 2 H = blockD S L ⊔ blockU0 S L) {g : G} (hg : g ∈ baum S)
    (hgC₁ : g ∈ centralizer (blockU L : Set G))
    (hgC₂ : g ∈ centralizer (blockU2 L s : Set G)) : g ∈ pCoreOf 2 H := by
  have hcs := hcfg.cs
  have h3 := hcfg.a3
  have hA := hcfg.isA4
  have hAs := hcfg.isA4s
  obtain ⟨hBL, -⟩ := (C56.baumann_A3_cs hcs h3).2
  have hsB : s ∈ normalizer (baum S : Set G) := mem_normalizer_baum hcfg.s_mem
  have hBLs : baum S ≤ normalizer (conjR L s : Set G) := C5.le_normalizer_conj hsB hBL
  have hBS : baum S ≤ S := inf_le_left
  have hUL : blockU L ≤ L := hA.le
  have hU₂Ls : blockU2 L s ≤ conjR L s := hAs.le
  have hUB : blockU L ≤ baum S := blockU_le_baum hcs h3
  have hU₂B : blockU2 L s ≤ baum S :=
    (C5.conjSubgroup_mono hUB s).trans (le_of_eq (C5.conjSubgroup_eq_self hsB))
  have hU0eq : blockU0 S L = blockU L ⊔ blockU2 L s := hcfg.blockU0_eq hU0
  obtain ⟨u₁, hu₁U, hu₁⟩ := hA.exists_inner (hBL hg)
    (fun u hu => (Subgroup.mem_centralizer_iff.mp hgC₁ u hu).symm)
  obtain ⟨u₂, hu₂U, hu₂⟩ := hAs.exists_inner (hBLs hg)
    (fun u hu => (Subgroup.mem_centralizer_iff.mp hgC₂ u hu).symm)
  have hu₁S : u₁ ∈ S := hBS (hUB hu₁U)
  have hu₂S : u₂ ∈ S := hBS (hU₂B hu₂U)
  have hu₁L : u₁ ∈ L := hUL hu₁U
  have hu₂Ls : u₂ ∈ conjR L s := hU₂Ls hu₂U
  have hc12 : u₁ * u₂ = u₂ * u₁ := hcfg.comm_elem u₁ hu₁L u₂ hu₂Ls
  obtain ⟨d, hd⟩ : ∃ d, d = (u₁ * u₂)⁻¹ * g := ⟨_, rfl⟩
  have hinv1 : (u₁ * u₂)⁻¹ = u₂⁻¹ * u₁⁻¹ := by group
  have hinv2 : (u₁ * u₂)⁻¹ = u₁⁻¹ * u₂⁻¹ := by rw [hc12]; group
  have hdL : ∀ l ∈ L, d * l = l * d := by
    intro l hl
    have e2 : u₂⁻¹ * l = l * u₂⁻¹ := by
      have h2 : u₂ * l = l * u₂ := (hcfg.comm_elem l hl u₂ hu₂Ls).symm
      calc u₂⁻¹ * l = u₂⁻¹ * (l * u₂) * u₂⁻¹ := by group
        _ = u₂⁻¹ * (u₂ * l) * u₂⁻¹ := by rw [← h2]
        _ = l * u₂⁻¹ := by group
    calc d * l = (u₁ * u₂)⁻¹ * (g * l * g⁻¹) * g := by rw [hd]; group
      _ = (u₁ * u₂)⁻¹ * (u₁ * l * u₁⁻¹) * g := by rw [hu₁ l hl]
      _ = (u₂⁻¹ * l) * u₁⁻¹ * g := by rw [hinv1]; group
      _ = (l * u₂⁻¹) * u₁⁻¹ * g := by rw [e2]
      _ = l * d := by rw [hd, hinv1]; group
  have hdLs : ∀ l ∈ conjR L s, d * l = l * d := by
    intro l hl
    have e1 : u₁⁻¹ * l = l * u₁⁻¹ := by
      have h2 : u₁ * l = l * u₁ := hcfg.comm_elem u₁ hu₁L l hl
      calc u₁⁻¹ * l = u₁⁻¹ * (l * u₁) * u₁⁻¹ := by group
        _ = u₁⁻¹ * (u₁ * l) * u₁⁻¹ := by rw [← h2]
        _ = l * u₁⁻¹ := by group
    calc d * l = (u₁ * u₂)⁻¹ * (g * l * g⁻¹) * g := by rw [hd]; group
      _ = (u₁ * u₂)⁻¹ * (u₂ * l * u₂⁻¹) * g := by rw [hu₂ l hl]
      _ = (u₁⁻¹ * l) * u₂⁻¹ * g := by rw [hinv2]; group
      _ = (l * u₁⁻¹) * u₂⁻¹ * g := by rw [e1]
      _ = l * d := by rw [hd, hinv2]; group
  have hdS : d ∈ S := by
    rw [hd]
    exact S.mul_mem (S.inv_mem (S.mul_mem hu₁S hu₂S)) (hBS hg)
  have hdC : d ∈ centralizer (conjJoin S L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [hcfg.join] at hy
    have hle : L ⊔ conjR L s ≤ centralizer ({d} : Set G) := by
      refine sup_le (fun l hl => ?_) (fun l hl => ?_)
      · refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
        rw [Set.mem_singleton_iff] at hh
        rw [hh]; exact hdL l hl
      · refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
        rw [Set.mem_singleton_iff] at hh
        rw [hh]; exact hdLs l hl
    exact (Subgroup.mem_centralizer_iff.mp (hle hy) d (Set.mem_singleton d)).symm
  have hu12 : u₁ * u₂ ∈ blockU0 S L := by
    rw [hU0eq]; exact mul_mem (mem_sup_left hu₁U) (mem_sup_right hu₂U)
  have hg' : g = (u₁ * u₂) * d := by rw [hd]; group
  rw [hQ, hg']
  exact mul_mem (mem_sup_right hu12) (mem_sup_left ⟨hdS, hdC⟩)

omit [Finite G] in
theorem conjR_eq_of_mem_diff {M₀ X : Subgroup G} (hSM : S ≤ M₀) (hidx : S.relIndex M₀ = 2)
    (hX : S ≤ normalizer (X : Set G)) {x y : G} (hx : x ∈ M₀) (hxS : x ∉ S) (hy : y ∈ M₀)
    (hyS : y ∉ S) : conjR X y = conjR X x := by
  have h1 : x⁻¹ * y ∈ S := inv_mul_mem_of_relIndex_two hidx hx hxS hy hyS
  have hxN : x ∈ normalizer (S : Set G) := normalizer_of_relIndex_two hSM hidx hx
  have h2 : y * x⁻¹ ∈ S := by
    have := (Subgroup.mem_normalizer_iff.mp hxN (x⁻¹ * y)).mp h1
    have e : x * (x⁻¹ * y) * x⁻¹ = y * x⁻¹ := by group
    rwa [e] at this
  show conjSubgroup X y = conjSubgroup X x
  calc conjSubgroup X y = conjSubgroup X ((y * x⁻¹) * x) := by
        rw [show (y * x⁻¹) * x = y by group]
    _ = conjSubgroup (conjSubgroup X (y * x⁻¹)) x := (conjSubgroup_conjSubgroup X _ _).symm
    _ = conjSubgroup X x := by rw [C5.conjSubgroup_eq_self (hX h2)]

theorem exists_good_of_mem_diff (hcfg : A3A3 T M H S L s)
    (hU0 : blockU0 S L = pCoreOf 2 (conjJoin S L))
    (hQ : pCoreOf 2 H = blockD S L ⊔ blockU0 S L) {M₀ : Subgroup G} (hSM : S ≤ M₀)
    (hMT : M₀ ≤ T) (hidx : S.relIndex M₀ = 2) {x : G} (hxM : x ∈ M₀) (hxS : x ∉ S) :
    ¬ conjSubgroup (blockU L) x ≤ centralizer (blockU L : Set G) ∨
      ¬ conjSubgroup (blockU L) (x * s⁻¹) ≤ centralizer (blockU L : Set G) := by
  have hcs := hcfg.cs
  by_contra hcon
  obtain ⟨h1, h2⟩ : conjSubgroup (blockU L) x ≤ centralizer (blockU L : Set G) ∧
      conjSubgroup (blockU L) (x * s⁻¹) ≤ centralizer (blockU L : Set G) :=
    ⟨not_not.mp fun h => hcon (Or.inl h), not_not.mp fun h => hcon (Or.inr h)⟩
  have hxQ := C56.not_conj_le_of_mem_diff hcs hSM hMT hidx hxM hxS
  apply hxQ
  have hxN : x ∈ normalizer (baum S : Set G) :=
    normalizer_le_normalizer_baum S (normalizer_of_relIndex_two hSM hidx hxM)
  have hUB : blockU L ≤ baum S := blockU_le_baum hcs hcfg.a3
  have hUxB : conjSubgroup (blockU L) x ≤ baum S :=
    (C5.conjSubgroup_mono hUB x).trans (le_of_eq (C5.conjSubgroup_eq_self hxN))
  have h2' : conjSubgroup (blockU L) x ≤ conjSubgroup (centralizer (blockU L : Set G)) s := by
    have h := C5.conjSubgroup_mono h2 s
    rw [conjSubgroup_conjSubgroup, show x * s⁻¹ * s = x by group] at h
    exact h
  rw [C5.conjSubgroup_centralizer] at h2'
  intro w hw
  exact mem_pCoreOf_of_centralizes hcfg hU0 hQ (hUxB hw) (h1 hw) (h2' hw)

theorem good_commutation (hD : AppC.C56DoubleA3)
    (hcfg : A3A3 T M H S L s) {M₀ : Subgroup G} (hSM : S ≤ M₀) (hMT : M₀ ≤ T)
    (hidx : S.relIndex M₀ = 2) {x : G} (hxM : x ∈ M₀) (hxS : x ∉ S)
    (hgood : ¬ conjSubgroup (blockU L) x ≤ centralizer (blockU L : Set G)) :
    ⁅blockU L ⊔ conjR (blockU L) x, blockU2 L s ⊔ conjR (blockU2 L s) x⁆ = ⊥ ∧
      ¬ conjSubgroup (blockU2 L s) x ≤ centralizer (blockU2 L s : Set G) := by
  have hcs := hcfg.cs
  have h3 := hcfg.a3
  have hs := hcfg.s_mem
  have hA := hcfg.isA4
  have hAs := hcfg.isA4s
  obtain ⟨hU0, -, hbD, hQ, -, -, hx⟩ := hD G T M H S L hcs hcfg.a3 hcfg.conjJoin_ne M₀ hSM hMT hidx
  obtain ⟨-, hbaum, -⟩ := hx x hxM hxS
  have hsB : s ∈ normalizer (baum S : Set G) := mem_normalizer_baum hs
  have hxNS : x ∈ normalizer (S : Set G) := normalizer_of_relIndex_two hSM hidx hxM
  have hxN : x ∈ normalizer (baum S : Set G) := normalizer_le_normalizer_baum S hxNS
  have hUB : blockU L ≤ baum S := blockU_le_baum hcs h3
  have hUxB : conjSubgroup (blockU L) x ≤ baum S :=
    (C5.conjSubgroup_mono hUB x).trans (le_of_eq (C5.conjSubgroup_eq_self hxN))
  have hnt₁ : ¬ baum S ≤ centralizer (blockU L : Set G) := fun h => hgood (hUxB.trans h)
  obtain ⟨z₁, -, -, -, R1⟩ := rank1_block₁ hcs h3 hnt₁
  have hU2B : blockU2 L s ≤ baum S := R1.conj_le_B hsB
  have hnt₂ : ¬ baum S ≤ centralizer (blockU2 L s : Set G) := by
    intro h
    apply hnt₁
    have h1 := (le_centralizer_iff_conj s⁻¹).mp h
    have e1 : conjSubgroup (blockU2 L s) s⁻¹ = blockU L :=
      C5.conjSubgroup_conjSubgroup_inv (blockU L) s
    rw [e1, C5.conjSubgroup_eq_self (inv_mem hsB)] at h1
    exact h1
  have hx1 : ¬ conjSubgroup (blockU L) x ≤ baum S ⊓ centralizer (blockU L : Set G) :=
    fun h => hgood (h.trans inf_le_right)
  have hsup : conjSubgroup (blockU L) x⁻¹ ⊔ (baum S ⊓ centralizer (blockU L : Set G)) = baum S :=
    R1.sup_Q_conj (inv_mem hxN) (by rw [inv_inv]; exact hx1)
  have hR : blockU L ⊔ conjSubgroup (baum S ⊓ centralizer (blockU L : Set G)) x = baum S := by
    have := congrArg (fun A => conjSubgroup A x) hsup
    simp only [C5.conjSubgroup_sup, C5.conjSubgroup_inv_conjSubgroup,
      C5.conjSubgroup_eq_self hxN] at this
    exact this
  have hbot : blockU L ⊓ blockU2 L s = ⊥ :=
    le_bot_iff.mp ((inf_le_inf hA.le hAs.le).trans (le_of_eq hcfg.inf_Ls))
  have hUN : blockU L ≤ normalizer
      ((conjSubgroup (baum S ⊓ centralizer (blockU L : Set G)) x : Subgroup G) : Set G) :=
    R1.U_le_B.trans (R1.B_le_normQ_conj hxN)
  have hI : ∀ a ∈ conjSubgroup (blockU L) x, ∀ v ∈ blockU2 L s, a * v = v * a := by
    intro a ha v hv
    have haB : a ∈ baum S := hUxB ha
    have hvR : v ∈ ((blockU L ⊔ conjSubgroup (baum S ⊓ centralizer (blockU L : Set G)) x :
        Subgroup G) : Set G) := by
      rw [hR]; exact hU2B hv
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hUN] at hvR
    obtain ⟨u, hu, c, hc, hvuc0⟩ := hvR
    have hvuc : u * c = v := hvuc0
    have hcc : c ∈ centralizer ((conjSubgroup (blockU L) x : Subgroup G) : Set G) := by
      have : c ∈ baum S ⊓ centralizer ((conjSubgroup (blockU L) x : Subgroup G) : Set G) := by
        rw [← R1.conj_Q_eq hxN]; exact hc
      exact this.2
    have hac : a * c = c * a := Subgroup.mem_centralizer_iff.mp hcc a ha
    have hca : c * a⁻¹ = a⁻¹ * c := by
      calc c * a⁻¹ = a⁻¹ * (a * c) * a⁻¹ := by group
        _ = a⁻¹ * (c * a) * a⁻¹ := by rw [hac]
        _ = a⁻¹ * c := by group
    have haU : a * u * a⁻¹ ∈ blockU L :=
      (Subgroup.mem_normalizer_iff.mp (R1.B_le_normU haB) u).mp hu
    have haV : a * v * a⁻¹ ∈ blockU2 L s :=
      (Subgroup.mem_normalizer_iff.mp (R1.B_le_normU_conj hsB haB) v).mp hv
    have ht : a * v * a⁻¹ * v⁻¹ = (a * u * a⁻¹) * u⁻¹ := by
      rw [← hvuc]
      calc a * (u * c) * a⁻¹ * (u * c)⁻¹ = a * u * (c * a⁻¹) * (c⁻¹ * u⁻¹) := by group
        _ = a * u * (a⁻¹ * c) * (c⁻¹ * u⁻¹) := by rw [hca]
        _ = (a * u * a⁻¹) * u⁻¹ := by group
    have hmem : a * v * a⁻¹ * v⁻¹ ∈ blockU L ⊓ blockU2 L s :=
      ⟨by rw [ht]; exact mul_mem haU ((blockU L).inv_mem hu),
        mul_mem haV ((blockU2 L s).inv_mem hv)⟩
    rw [hbot] at hmem
    have h1 : a * v * a⁻¹ * v⁻¹ = 1 := Subgroup.mem_bot.mp hmem
    calc a * v = (a * v * a⁻¹ * v⁻¹) * v * a := by group
      _ = v * a := by rw [h1]; group
  have hxx : x * x ∈ S := mul_self_mem_of_relIndex_two hidx hxM hxS
  have hperm : conjSubgroup (blockU2 L s) x⁻¹ = conjSubgroup (blockU L) x ∨
      conjSubgroup (blockU2 L s) x⁻¹ = conjSubgroup (blockU2 L s) x := by
    obtain ⟨g, hg⟩ : ∃ g : G, g = (x * x)⁻¹ := ⟨_, rfl⟩
    have hgS : g ∈ S := by rw [hg]; exact S.inv_mem hxx
    obtain ⟨g', hg'⟩ : ∃ g' : G, g' = x * g * x⁻¹ := ⟨_, rfl⟩
    have hg'S : g' ∈ S := by rw [hg']; exact (Subgroup.mem_normalizer_iff.mp hxNS g).mp hgS
    have e1 : x⁻¹ = g' * x := by rw [hg', hg]; group
    have hsg : s * g' ∈ S := S.mul_mem hs hg'S
    have e2 : conjSubgroup (blockU2 L s) x⁻¹ =
        conjSubgroup (conjSubgroup (blockU L) (s * g')) x := by
      show conjSubgroup (conjSubgroup (blockU L) s) x⁻¹ = _
      rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup, e1, mul_assoc]
    rcases hcfg.conj_cases hU0 hsg with ⟨h1, -⟩ | ⟨h1, -⟩
    · left
      rw [e2]
      have : conjSubgroup (blockU L) (s * g') = blockU L := h1
      rw [this]
    · right
      rw [e2]
      have : conjSubgroup (blockU L) (s * g') = blockU2 L s := h1
      rw [this]
  have hII' : ∀ a ∈ blockU L, ∀ b ∈ conjSubgroup (blockU2 L s) x⁻¹, a * b = b * a := by
    intro a ha b hb
    have hv : x⁻¹ * b * x ∈ blockU2 L s := by
      have := mem_conjSubgroup_iff.mp hb
      simpa using this
    have ha₁ : x⁻¹ * a * x ∈ conjSubgroup (blockU L) x := by
      rw [mem_conjSubgroup_iff]
      have e : x * (x⁻¹ * a * x) * x⁻¹ = a := by group
      rw [e]; exact ha
    have h := hI _ ha₁ _ hv
    calc a * b = x * (x⁻¹ * a * x * (x⁻¹ * b * x)) * x⁻¹ := by group
      _ = x * (x⁻¹ * b * x * (x⁻¹ * a * x)) * x⁻¹ := by rw [h]
      _ = b * a := by group
  have hII : ∀ a ∈ blockU L, ∀ b ∈ conjSubgroup (blockU2 L s) x, a * b = b * a := by
    rcases hperm with hp | hp
    · exfalso
      apply hgood
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      exact hII' u hu a (by rw [hp]; exact ha)
    · rw [hp] at hII'; exact hII'
  have hc0 : ⁅blockU L ⊔ conjR (blockU L) x, blockU2 L s ⊔ conjR (blockU2 L s) x⁆ = ⊥ := by
    refine commutator_sup_sup_eq_bot ?_ ?_ ?_ ?_
    · exact fun a ha c hc => hcfg.comm_elem a (hA.le ha) c (hAs.le hc)
    · exact fun a ha d hd => hII a ha d hd
    · exact fun b hb c hc => hI b hb c hc
    · intro b hb d hd
      have hb' : x * b * x⁻¹ ∈ blockU L := mem_conjR.mp hb
      have hd' : x * d * x⁻¹ ∈ blockU2 L s := mem_conjR.mp hd
      have h := hcfg.comm_elem _ (hA.le hb') _ (hAs.le hd')
      calc b * d = x⁻¹ * ((x * b * x⁻¹) * (x * d * x⁻¹)) * x := by group
        _ = x⁻¹ * ((x * d * x⁻¹) * (x * b * x⁻¹)) * x := by rw [h]
        _ = d * b := by group
  refine ⟨hc0, ?_⟩
  intro hle
  apply hnt₂
  have hU0eq : blockU0 S L = blockU L ⊔ blockU2 L s := hcfg.blockU0_eq hU0
  have e : conjR (blockU0 S L) x = conjSubgroup (blockU L) x ⊔ conjSubgroup (blockU2 L s) x := by
    rw [hU0eq]; exact C5.conjSubgroup_sup _ _ _
  rw [hbaum, e]
  refine sup_le (sup_le ?_ ?_) (sup_le ?_ hle)
  · intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hu' : u ∈ conjJoin S L := by
      rw [hcfg.join]; exact mem_sup_right (hAs.le hu)
    exact Subgroup.mem_centralizer_iff.mp hd.2 u hu'
  · rw [hU0eq]
    refine sup_le (fun u hu => ?_) (fun u hu => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact (hcfg.comm_elem u (hA.le hu) v (hAs.le hv)).symm
    · rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact hAs.comm_U v hv u hu
  · intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (hI a ha v hv).symm

theorem exists_good_elt (hD : AppC.C56DoubleA3)
    (hcfg : A3A3 T M H S L s) {M₀ : Subgroup G} (hSM : S ≤ M₀) (hMT : M₀ ≤ T)
    (hidx : S.relIndex M₀ = 2) :
    ∃ x ∈ M₀, x ∉ S ∧ ¬ conjSubgroup (blockU L) x ≤ centralizer (blockU L : Set G) ∧
      ⁅blockU L ⊔ conjR (blockU L) x, blockU2 L s ⊔ conjR (blockU2 L s) x⁆ = ⊥ ∧
      ¬ conjSubgroup (blockU2 L s) x ≤ centralizer (blockU2 L s : Set G) ∧
      ¬ conjSubgroup (blockU L) x⁻¹ ≤ centralizer (blockU L : Set G) ∧
      ¬ conjSubgroup (blockU2 L s) x⁻¹ ≤ centralizer (blockU2 L s : Set G) := by
  have hcs := hcfg.cs
  obtain ⟨hU0, -, hbD, hQ, -, -, -⟩ := hD G T M H S L hcs hcfg.a3 hcfg.conjJoin_ne M₀ hSM hMT hidx
  have hQ' : pCoreOf 2 H = blockD S L ⊔ blockU0 S L := by rw [← hbD]; exact hQ
  obtain ⟨x₀, hx₀M, hx₀S⟩ : ∃ x ∈ M₀, x ∉ S := by
    by_contra hcon
    have hle : M₀ ≤ S := fun x hx => by
      by_contra h; exact hcon ⟨x, hx, h⟩
    have := (Subgroup.relIndex_eq_one (H := S) (K := M₀)).mpr hle
    omega
  have key : ∀ y ∈ M₀, y ∉ S →
      ¬ conjSubgroup (blockU L) y ≤ centralizer (blockU L : Set G) →
      ∃ x ∈ M₀, x ∉ S ∧ ¬ conjSubgroup (blockU L) x ≤ centralizer (blockU L : Set G) ∧
        ⁅blockU L ⊔ conjR (blockU L) x, blockU2 L s ⊔ conjR (blockU2 L s) x⁆ = ⊥ ∧
        ¬ conjSubgroup (blockU2 L s) x ≤ centralizer (blockU2 L s : Set G) ∧
        ¬ conjSubgroup (blockU L) x⁻¹ ≤ centralizer (blockU L : Set G) ∧
        ¬ conjSubgroup (blockU2 L s) x⁻¹ ≤ centralizer (blockU2 L s : Set G) := by
    intro y hyM hyS hgood
    obtain ⟨hc0, hc2⟩ := good_commutation hD hcfg hSM hMT hidx hyM hyS hgood
    have hyiM : y⁻¹ ∈ M₀ := inv_mem hyM
    have hyiS : y⁻¹ ∉ S := fun h => hyS (by simpa using S.inv_mem h)
    have hgoodi := not_conj_inv_le_centralizer hgood
    obtain ⟨-, hci2⟩ := good_commutation hD hcfg hSM hMT hidx hyiM hyiS hgoodi
    exact ⟨y, hyM, hyS, hgood, hc0, hc2, hgoodi, hci2⟩
  rcases exists_good_of_mem_diff hcfg hU0 hQ' hSM hMT hidx hx₀M hx₀S with h | h
  · exact key x₀ hx₀M hx₀S h
  · have hxsM : x₀ * s⁻¹ ∈ M₀ := mul_mem hx₀M (inv_mem (hSM hcfg.s_mem))
    have hxsS : x₀ * s⁻¹ ∉ S := fun hh => hx₀S (by simpa using S.mul_mem hh hcfg.s_mem)
    exact key _ hxsM hxsS h

theorem lemma2_4_31_exists (hD : AppC.C56DoubleA3) :
    ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G) (s : G), A3A3 T M H S L s →
      ∃ x z₁ z₂ : G, A3A3x T M H S L s x z₁ z₂ := by
  intro G _ _ T M H S L s hcfg
  have hcs := hcfg.cs
  have h3 := hcfg.a3
  have hs := hcfg.s_mem
  have hsB : s ∈ normalizer (baum S : Set G) := mem_normalizer_baum hs
  obtain ⟨M₀, hSM, hMT, hidx⟩ := C56.exists_index_two hcs
  obtain ⟨x, hxM, hxS, hc1, -, hc2, hci1, hci2⟩ := exists_good_elt hD hcfg hSM hMT hidx
  have hxN : x ∈ normalizer (baum S : Set G) :=
    normalizer_le_normalizer_baum S (normalizer_of_relIndex_two hSM hidx hxM)
  have hUB : blockU L ≤ baum S := blockU_le_baum hcs h3
  have hUxB : ∀ g ∈ normalizer (baum S : Set G), conjSubgroup (blockU L) g ≤ baum S :=
    fun g hg => (C5.conjSubgroup_mono hUB g).trans (le_of_eq (C5.conjSubgroup_eq_self hg))
  have hnt₁ : ¬ baum S ≤ centralizer (blockU L : Set G) := fun h => hc1 ((hUxB x hxN).trans h)
  obtain ⟨z₁, hz₁U, hz₁1, hz₁C, R1⟩ := rank1_block₁ hcs h3 hnt₁
  have hU2B : blockU2 L s ≤ baum S := R1.conj_le_B hsB
  have hnt₂ : ¬ baum S ≤ centralizer (blockU2 L s : Set G) := fun h =>
    hc2 (((C5.conjSubgroup_mono hU2B x).trans (le_of_eq (C5.conjSubgroup_eq_self hxN))).trans h)
  obtain ⟨z₂', hz₂'U, hz₂'1, hz₂'C, R2⟩ := rank1_block₂ hcs h3 hs R1 hnt₂
  obtain ⟨-, -, hU2, -, -⟩ := (hcs.block.1.1 : IsShort2 L).alt3_structure h3
  have hz₁2 : z₁ ^ 2 = 1 := hU2 z₁ hz₁U
  have hz₂'2 : z₂' ^ 2 = 1 := by
    have ha' : s * z₂' * s⁻¹ ∈ blockU L := mem_conjR.mp hz₂'U
    have h1 : (s * z₂' * s⁻¹) * (s * z₂' * s⁻¹) = 1 := by
      have := hU2 _ ha'
      rwa [pow_two] at this
    have : z₂' * z₂' = s⁻¹ * ((s * z₂' * s⁻¹) * (s * z₂' * s⁻¹)) * s := by group
    rw [h1] at this
    rw [pow_two, this]; group
  have hx1 : ¬ conjSubgroup (blockU L) x ≤ baum S ⊓ centralizer (blockU L : Set G) :=
    fun h => hc1 (h.trans inf_le_right)
  have hx2 : ¬ conjSubgroup (blockU L) x⁻¹ ≤ baum S ⊓ centralizer (blockU L : Set G) :=
    fun h => hci1 (h.trans inf_le_right)
  have hW1 := R1.conj_W hxN hx1 hx2
  have hxz₁ : x * z₁ = z₁ * x := by
    have hmem : x⁻¹ * z₁ * x ∈ conjSubgroup (zpowers z₁) x := by
      rw [mem_conjSubgroup_iff]
      have : x * (x⁻¹ * z₁ * x) * x⁻¹ = z₁ := by group
      rw [this]; exact Subgroup.mem_zpowers z₁
    rw [hW1] at hmem
    rcases (mem_zpowers_iff_of_sq_eq_one hz₁2).mp hmem with h | h
    · exfalso
      apply hz₁1
      calc z₁ = x * (x⁻¹ * z₁ * x) * x⁻¹ := by group
        _ = 1 := by rw [h]; group
    · calc x * z₁ = x * (x⁻¹ * z₁ * x) := by rw [h]
        _ = z₁ * x := by group
  have hz₂U : s⁻¹ * z₁ * s ∈ blockU2 L s := by
    refine mem_conjR.mpr ?_
    have : s * (s⁻¹ * z₁ * s) * s⁻¹ = z₁ := by group
    rw [this]; exact hz₁U
  have hz₁C' : z₁ ∈ centralizer (baum S : Set G) := by
    have : z₁ ∈ blockU L ⊓ centralizer (baum S : Set G) := by
      rw [hz₁C]; exact Subgroup.mem_zpowers z₁
    exact this.2
  have hz₂C : s⁻¹ * z₁ * s ∈ centralizer (baum S : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hh' : s * h * s⁻¹ ∈ baum S := (Subgroup.mem_normalizer_iff.mp hsB h).mp hh
    have e : (s * h * s⁻¹) * z₁ = z₁ * (s * h * s⁻¹) :=
      Subgroup.mem_centralizer_iff.mp hz₁C' _ hh'
    calc h * (s⁻¹ * z₁ * s) = s⁻¹ * ((s * h * s⁻¹) * z₁) * s := by group
      _ = s⁻¹ * (z₁ * (s * h * s⁻¹)) * s := by rw [e]
      _ = s⁻¹ * z₁ * s * h := by group
  have hz₂1 : s⁻¹ * z₁ * s ≠ 1 := by
    intro h
    apply hz₁1
    calc z₁ = s * (s⁻¹ * z₁ * s) * s⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hz₂eq : s⁻¹ * z₁ * s = z₂' := by
    have hmem : s⁻¹ * z₁ * s ∈ blockU2 L s ⊓ centralizer (baum S : Set G) := ⟨hz₂U, hz₂C⟩
    rw [hz₂'C] at hmem
    rcases (mem_zpowers_iff_of_sq_eq_one hz₂'2).mp hmem with h | h
    · exact absurd h hz₂1
    · exact h
  have hx1' : ¬ conjSubgroup (blockU2 L s) x ≤ baum S ⊓ centralizer (blockU2 L s : Set G) :=
    fun h => hc2 (h.trans inf_le_right)
  have hx2' : ¬ conjSubgroup (blockU2 L s) x⁻¹ ≤ baum S ⊓ centralizer (blockU2 L s : Set G) :=
    fun h => hci2 (h.trans inf_le_right)
  have hW2 := R2.conj_W hxN hx1' hx2'
  have hxz₂ : x * z₂' = z₂' * x := by
    have hmem : x⁻¹ * z₂' * x ∈ conjSubgroup (zpowers z₂') x := by
      rw [mem_conjSubgroup_iff]
      have : x * (x⁻¹ * z₂' * x) * x⁻¹ = z₂' := by group
      rw [this]; exact Subgroup.mem_zpowers z₂'
    rw [hW2] at hmem
    rcases (mem_zpowers_iff_of_sq_eq_one hz₂'2).mp hmem with h | h
    · exfalso
      apply hz₂'1
      calc z₂' = x * (x⁻¹ * z₂' * x) * x⁻¹ := by group
        _ = 1 := by rw [h]; group
    · calc x * z₂' = x * (x⁻¹ * z₂' * x) := by rw [h]
        _ = z₂' * x := by group
  refine ⟨x, z₁, s⁻¹ * z₁ * s, ?_⟩
  exact
    { toA3A3 := hcfg
      x_mem := hMT hxM
      x_not_mem := hxS
      x_good := hc1
      x_good₂ := hc2
      z₁_gen := hz₁C.symm
      z₁_ne := hz₁1
      z₂_def := rfl
      x_comm₁ := hxz₁
      x_comm₂ := by rw [hz₂eq]; exact hxz₂ }

end CFSG.QuasithinUnique.DoubleA3
