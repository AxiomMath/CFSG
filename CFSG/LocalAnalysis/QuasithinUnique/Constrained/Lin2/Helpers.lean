module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PGroup.NormalSubgroups
public import CFSG.Quasithin.Background.B2Thompson
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Open.FusionDefs

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin

section Center

variable {G : Type*} [Group G] [Finite G]

theorem exists_mem_inf_center_of_normal {T Z : Subgroup G} (hT : IsPGroup 2 T) (hZT : Z ≤ T)
    (hZn : T ≤ Subgroup.normalizer (Z : Set G)) (hZ : Z ≠ ⊥) :
    ∃ z ∈ Z, z ≠ 1 ∧ z ∈ Subgroup.centralizer (T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 T) := ⟨hT⟩
  have hnorm : (Z.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hZn
  obtain ⟨⟨z₀, hz₀⟩, hz₀1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hZ
  have hz₀1 : z₀ ≠ 1 := fun h => hz₀1' (Subtype.ext h)
  have : Nontrivial (Z.subgroupOf T) := by
    refine ⟨⟨1, ?_⟩⟩
    have hz : (⟨z₀, hZT hz₀⟩ : T) ∈ Z.subgroupOf T := hz₀
    refine ⟨⟨⟨z₀, hZT hz₀⟩, hz⟩, ?_⟩
    intro h
    apply hz₀1
    have := congrArg (fun y : Z.subgroupOf T => ((y : T) : G)) h
    exact (by simpa using this : (1 : G) = z₀).symm
  obtain ⟨x, hx1, hxc⟩ := CFSG.exists_nontrivial_center_mem_normal (Z.subgroupOf T) (p := 2)
  refine ⟨((x : T) : G), x.2, ?_, ?_⟩
  · intro h
    apply hx1
    apply Subtype.ext
    apply Subtype.ext
    simpa using h
  · rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have := Subgroup.mem_center_iff.1 hxc ⟨t, ht⟩
    simpa using congrArg Subtype.val this

end Center

section Thompson

variable {G : Type*} [Group G] [Finite G]

theorem thompsonJ_eq_of_le {T P : Subgroup G} (hJ : thompsonJ T ≤ P) (hPT : P ≤ T) :
    thompsonJ P = thompsonJ T := by
  obtain ⟨A', hA'⟩ := exists_isMaxElemAbelian T
  have hA'P : A' ≤ P := (le_iSup₂_of_le A' hA' le_rfl : A' ≤ thompsonJ T).trans hJ
  have key : ∀ A : Subgroup G, IsMaxElemAbelian P A ↔ IsMaxElemAbelian T A := by
    intro A
    constructor
    · rintro ⟨hAP, hAe, hAmax⟩
      refine ⟨hAP.trans hPT, hAe, fun B hBT hBe => ?_⟩
      exact (hA'.2.2 B hBT hBe).trans (hAmax A' hA'P hA'.2.1)
    · intro hA
      have hAJ : A ≤ thompsonJ T := le_iSup₂_of_le A hA le_rfl
      exact ⟨hAJ.trans hJ, hA.2.1, fun B hBP hBe => hA.2.2 B (hBP.trans hPT) hBe⟩
  unfold thompsonJ
  exact iSup_congr fun A => iSup_congr_Prop (key A) fun _ => rfl

omit [Finite G] in
theorem zpow_of_sq_eq_one {z : G} (hz : z ^ 2 = 1) (k : ℤ) : z ^ k = 1 ∨ z ^ k = z := by
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left; rw [zpow_mul]; simp [hz]
  · right; rw [zpow_add, zpow_mul]; simp [hz]

omit [Finite G] in
theorem centralizer_singleton_eq_normalizer_zpowers {z : G} (hz : z ^ 2 = 1) (hz1 : z ≠ 1) :
    Subgroup.centralizer ({z} : Set G) = Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro hg y
    have hc : Commute g z := hg
    have hc' : ∀ k : ℤ, g * z ^ k = z ^ k * g := fun k => (hc.zpow_right k).eq
    constructor
    · intro hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
      rw [hc' k]; group
    · intro hy
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hy
      refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
      have : g * y = g * z ^ k := by rw [hc' k, hk]; group
      exact (mul_left_cancel this).symm
  · intro hn
    have h1 := (hn z).1 (Subgroup.mem_zpowers z)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h1
    have hne : g * z * g⁻¹ ≠ 1 := by
      intro h
      apply hz1
      have : z = g⁻¹ * (g * z * g⁻¹) * g := by group
      rw [this, h]; group
    rcases zpow_of_sq_eq_one hz k with h | h
    · exact absurd (hk.symm.trans h) hne
    · have : g * z * g⁻¹ = z := hk.symm.trans h
      calc g * z = (g * z * g⁻¹) * g := by group
        _ = z * g := by rw [this]

omit [Finite G] in
theorem isTwoLocal_centralizer_of_sq_eq_one {z : G} (hz : z ^ 2 = 1) (hz1 : z ≠ 1) :
    IsTwoLocal (Subgroup.centralizer ({z} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨Subgroup.zpowers z, ?_, ?_, centralizer_singleton_eq_normalizer_zpowers hz hz1⟩
  · intro h
    apply hz1
    have : z ∈ Subgroup.zpowers z := Subgroup.mem_zpowers z
    rw [h] at this
    simpa using this
  · refine IsPGroup.of_card (n := 1) ?_
    have : orderOf z = 2 := orderOf_eq_prime hz hz1
    rw [Nat.card_zpowers, this]; simp

end Thompson

section TI

variable {G : Type*} [Group G]

theorem mem_of_inf_conj_ne_bot_aux {U M : Subgroup G}
    (hcent : ∀ u ∈ U, u ≠ 1 → Subgroup.centralizer ({u} : Set G) ≤ M)
    (hfus : ∀ u ∈ U, ∀ g : G, g⁻¹ * u * g ∈ U → ∃ m ∈ M, g⁻¹ * u * g = m⁻¹ * u * m)
    {g : G} (hg : U ⊓ U.map (MulAut.conj g).toMonoidHom ≠ ⊥) : g ∈ M := by
  obtain ⟨⟨v, hv⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hg
  obtain ⟨hvU, u, huU, huv⟩ := Subgroup.mem_inf.mp hv
  have huv' : g * u * g⁻¹ = v := by simpa [MulAut.conj_apply] using huv
  have hu1 : u ≠ 1 := by
    rintro rfl
    apply hv1
    ext
    simpa using huv'.symm
  have hconj : g⁻¹⁻¹ * u * g⁻¹ ∈ U := by simpa [huv'] using hvU
  obtain ⟨m, hmM, hm⟩ := hfus u huU g⁻¹ hconj
  have hcomm : m * g ∈ Subgroup.centralizer ({u} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : g * u * g⁻¹ = m⁻¹ * u * m := by simpa using hm
    calc m * g * u = m * (g * u * g⁻¹) * g := by group
      _ = m * (m⁻¹ * u * m) * g := by rw [h1]
      _ = u * (m * g) := by group
  have hmg : m * g ∈ M := hcent u huU hu1 hcomm
  have : g = m⁻¹ * (m * g) := by group
  rw [this]
  exact M.mul_mem (M.inv_mem hmM) hmg

theorem fusionIsTI_of_centralizer_le {U M : Subgroup G}
    (hM : Subgroup.normalizer (U : Set G) = M)
    (hcent : ∀ u ∈ U, u ≠ 1 → Subgroup.centralizer ({u} : Set G) ≤ M)
    (hfus : ∀ u ∈ U, ∀ g : G, g⁻¹ * u * g ∈ U → ∃ m ∈ M, g⁻¹ * u * g = m⁻¹ * u * m) :
    fusionIsTI U := by
  intro g hne
  by_contra hbot
  apply hne
  have hgM : g ∈ Subgroup.normalizer (U : Set G) :=
    hM ▸ mem_of_inf_conj_ne_bot_aux hcent hfus hbot
  ext x
  simp only [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply] using (Subgroup.mem_normalizer_iff.mp hgM y).mp hy
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgM) x).mp hx
    simpa using this

end TI

end CFSG.QuasithinUnique.Lin2
