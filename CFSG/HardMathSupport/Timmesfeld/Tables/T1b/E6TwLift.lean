module

public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6Lift
public import CFSG.RankThree.PartTwo.Census.Exceptional.TwistedE6Local

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.T1b

open CFSG.Open CFSG.SectionRank CFSG.RankThree.PartTwo.Census.Exceptional

section Lift

variable {L Q : Type*} [Group L] [Group Q]

theorem exists_elemAbelian_of_reflection_lifts' (π : L →* Q) (hπ : Function.Surjective π)
    (hc : ∀ x, π x = 1 → x ∈ Subgroup.center L) {ι : Type*} (e n : ι → Q)
    (hcomm : ∀ i j, e i * e j = e j * e i) (he : ∀ i, e i ^ 3 = 1)
    (hinv : ∀ i, n i * e i * (n i)⁻¹ = (e i)⁻¹)
    (hrel : ∀ i j, (∃ k : ℤ, n i * e j * (n i)⁻¹ = e j * e i ^ k) ∨
      (∃ k : ℤ, n j * e i * (n j)⁻¹ = e i * e j ^ k)) :
    ∃ R : Subgroup L, (∀ x ∈ R, x ^ 3 = 1) ∧ (∀ x ∈ R, ∀ y ∈ R, x * y = y * x) ∧
      R.map π = Subgroup.closure (Set.range e) := by
  have hcen : ∀ x, π x = 1 → ∀ g, g * x = x * g := fun x hx g =>
    Subgroup.mem_center_iff.1 (hc x hx) g
  choose a₀ ha₀ using fun i => hπ (e i)
  choose N hN using fun i => hπ (n i)
  have hcor : ∀ i, ∃ a : L, π a = e i ∧ a ^ 3 = 1 := by
    intro i
    set z := N i * a₀ i * (N i)⁻¹ * a₀ i with hz
    set w := a₀ i ^ 3 with hw
    have hπz : π z = 1 := by
      simp only [hz, map_mul, map_inv, hN, ha₀, hinv, inv_mul_cancel]
    have hπw : π w = 1 := by simp only [hw, map_pow, ha₀, he]
    have hu : π (w⁻¹ * z) = 1 := by rw [map_mul, map_inv, hπw, hπz]; simp
    refine ⟨a₀ i * (w⁻¹ * z), by rw [map_mul, hu, ha₀, mul_one], ?_⟩
    exact exists_cube_adjust (hcen z hπz) (hcen w hπw)
      (a := a₀ i) (N := N i) (by simp only [hz]; group) rfl
  choose a ha ha3 using hcor
  have hpair₀ : ∀ i j (k : ℤ), n i * e j * (n i)⁻¹ = e j * e i ^ k → a i * a j = a j * a i := by
    intro i j k hk
    set y₁ := N i * a i * (N i)⁻¹ * a i with hy₁
    set y₂ := (a j * a i ^ k)⁻¹ * (N i * a j * (N i)⁻¹) with hy₂
    have hπy₁ : π y₁ = 1 := by
      simp only [hy₁, map_mul, map_inv, hN, ha, hinv, inv_mul_cancel]
    have hπy₂ : π y₂ = 1 := by
      simp only [hy₂, map_mul, map_inv, map_zpow, hN, ha]
      rw [hk]; group
    have hcc : π (a i * a j * (a i)⁻¹ * (a j)⁻¹) = 1 := by
      simp only [map_mul, map_inv, ha]
      rw [hcomm i j]; group
    have := comm_eq_one_of_reflection (hcen y₁ hπy₁) (hcen y₂ hπy₂) (hcen _ hcc) (ha3 i)
      (a := a i) (b := a j) (N := N i) (k := k) (by simp only [hy₁]; group)
      (by simp only [hy₂]; group)
    calc a i * a j = a i * a j * (a i)⁻¹ * (a j)⁻¹ * (a j * a i) := by group
      _ = a j * a i := by rw [this, one_mul]
  have hpair : ∀ i j, a i * a j = a j * a i := by
    intro i j
    rcases hrel i j with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact hpair₀ i j k hk
    · exact (hpair₀ j i k hk).symm
  have hpw : (Set.range a).Pairwise Commute := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ -
    exact hpair i j
  have hcl := Subgroup.isMulCommutative_closure hpw
  have hRc : ∀ x ∈ Subgroup.closure (Set.range a), ∀ y ∈ Subgroup.closure (Set.range a),
      x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hcl.is_comm.comm (⟨x, hx⟩ : Subgroup.closure (Set.range a)) ⟨y, hy⟩)
  refine ⟨Subgroup.closure (Set.range a), ?_, hRc, ?_⟩
  · intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact ha3 i
    | one => simp
    | mul x y hx hy hx3 hy3 =>
      have := hRc x hx y hy
      rw [(show Commute x y from this).mul_pow, hx3, hy3, one_mul]
    | inv x hx hx3 => rw [inv_pow, hx3, inv_one]
  · rw [MonoidHom.map_closure]
    congr 1
    ext x
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩; exact ⟨i, (ha i).symm⟩
    · rintro ⟨i, rfl⟩; exact ⟨_, ⟨i, rfl⟩, ha i⟩

end Lift

section Count

variable {Q : Type*} [Group Q] [Finite Q]

omit [Finite Q] in
theorem isElemAbelian_closure {ι : Type*} (g : ι → Q) (hg : ∀ i j, Commute (g i) (g j))
    (hg3 : ∀ i, g i ^ 3 = 1) : IsElemAbelian 3 (Subgroup.closure (Set.range g)) := by
  have hpw : (Set.range g).Pairwise Commute := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ -
    exact hg i j
  have hcl := Subgroup.isMulCommutative_closure hpw
  refine ⟨hcl, fun x hx => ?_⟩
  have hRc : ∀ x ∈ Subgroup.closure (Set.range g), ∀ y ∈ Subgroup.closure (Set.range g),
      x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hcl.is_comm.comm (⟨x, hx⟩ : Subgroup.closure (Set.range g)) ⟨y, hy⟩)
  induction hx using Subgroup.closure_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hg3 i
  | one => simp
  | mul x y hx hy hx3 hy3 =>
    rw [(show Commute x y from hRc x hx y hy).mul_pow, hx3, hy3, one_mul]
  | inv x hx hx3 => rw [inv_pow, hx3, inv_one]

theorem three_pow_card_le_card_closure {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → Q)
    (hg : ∀ i j, Commute (g i) (g j))
    (S : ι → Subgroup Q) (hS : ∀ i j, i ≠ j → g j ∈ S i) (hSg : ∀ i, g i ∉ S i)
    (hg3 : ∀ i, g i ^ 3 = 1) :
    3 ^ Fintype.card ι ≤ Nat.card (Subgroup.closure (Set.range g)) := by
  set Y := Subgroup.closure (Set.range g)
  have hpw : (Set.range g).Pairwise Commute := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ -
    exact hg i j
  have hYc : IsMulCommutative Y := Subgroup.isMulCommutative_closure hpw
  have hcomm : ∀ a b : Y, a * b = b * a := fun a b => mul_comm' a b
  let : CommGroup Y := { (inferInstance : Group Y) with mul_comm := hcomm }
  let g' : ι → Y := fun i => ⟨g i, Subgroup.subset_closure ⟨i, rfl⟩⟩
  have hgen : Subgroup.closure (Set.range g') = ⊤ := by
    rw [eq_top_iff, ← Subgroup.closure_closure_coe_preimage (k := Set.range g)]
    refine Subgroup.closure_mono ?_
    rintro x ⟨i, hi⟩
    exact ⟨i, Subtype.ext hi⟩
  have hbound := CFSG.RankThree.Theta.three_pow_card_le_card_ker_pow g' hgen
    (fun i => (S i).subgroupOf Y) (fun i j hij => Subgroup.mem_subgroupOf.2 (hS i j hij))
    (fun i h => hSg i (Subgroup.mem_subgroupOf.1 h))
    (fun i => by
      have : g' i ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hg3 i)
      rw [this]
      exact Subgroup.one_mem _)
  exact hbound.trans (Nat.card_mono (Set.toFinite _) (Set.subset_univ _) |>.trans
    (le_of_eq (Nat.card_univ)))

variable (e y : Fin 4 → Q) (f u : Q)

theorem three_pow_five_le_card_closure (hee : ∀ i j, Commute (e i) (e j))
    (hef : ∀ i, Commute (e i) f) (he3 : ∀ i, e i ^ 3 = 1) (hf3 : f ^ 3 = 1) (hf1 : f ≠ 1)
    (hy : ∀ i j, i ≠ j → Commute (y i) (e j)) (hyf : ∀ i, Commute (y i) f)
    (hyi : ∀ i, ¬ Commute (y i) (e i)) :
    3 ^ 5 ≤ Nat.card (Subgroup.closure (Set.range fun o : Option (Fin 4) => o.elim f e)) := by
  set g : Option (Fin 4) → Q := fun o => o.elim f e
  have hg : ∀ i j, Commute (g i) (g j) := by
    rintro (_ | a) (_ | b)
    · exact Commute.refl _
    · exact (hef b).symm
    · exact hef a
    · exact hee a b
  let S : Option (Fin 4) → Subgroup Q := fun o => o.elim (Subgroup.closure (Set.range e))
    fun i => Subgroup.centralizer ({y i} : Set Q)
  have h := three_pow_card_le_card_closure g hg S
    (by
      rintro (_ | a) (_ | b) hab
      · exact absurd rfl hab
      · exact Subgroup.subset_closure ⟨b, rfl⟩
      · exact Subgroup.mem_centralizer_singleton_iff.2 (hyf a).eq.symm
      · exact Subgroup.mem_centralizer_singleton_iff.2
          (hy a b fun h => hab (h ▸ rfl)).eq.symm)
    (by
      rintro (_ | a) h
      · exact hf1 (eq_one_of_mem_closure e f y hee he3 hy hyf hyi h)
      · exact hyi a (Subgroup.mem_centralizer_singleton_iff.1 h).symm)
    (by
      rintro (_ | a)
      · exact hf3
      · exact he3 a)
  simpa using h

theorem three_pow_six_le_card_closure (hee : ∀ i j, Commute (e i) (e j))
    (hef : ∀ i, Commute (e i) f) (heu : ∀ i, Commute (e i) u) (hfu : Commute f u)
    (he3 : ∀ i, e i ^ 3 = 1) (hf3 : f ^ 3 = 1) (hu3 : u ^ 3 = 1)
    (hy : ∀ i j, i ≠ j → Commute (y i) (e j)) (hyf : ∀ i, Commute (y i) f)
    (hyu : ∀ i, Commute (y i) u) (hyi : ∀ i, ¬ Commute (y i) (e i))
    (hind : ∀ a c : ℤ, f ^ a * u ^ c = 1 → (3 : ℤ) ∣ a ∧ (3 : ℤ) ∣ c) :
    3 ^ 6 ≤ Nat.card (Subgroup.closure
      (Set.range fun o : Option (Option (Fin 4)) => o.elim u fun o' => o'.elim f e)) := by
  set g : Option (Option (Fin 4)) → Q := fun o => o.elim u fun o' => o'.elim f e
  have hg : ∀ i j, Commute (g i) (g j) := by
    rintro (_ | _ | a) (_ | _ | b)
    · exact Commute.refl _
    · exact hfu.symm
    · exact (heu b).symm
    · exact hfu
    · exact Commute.refl _
    · exact (hef b).symm
    · exact heu a
    · exact hef a
    · exact hee a b
  have hdecomp : ∀ v : Q, (∀ i, Commute (e i) v) → ∀ w ∈ Subgroup.closure (Set.range e) ⊔
      Subgroup.zpowers v, ∃ x ∈ Subgroup.closure (Set.range e), ∃ c : ℤ, w = x * v ^ c := by
    intro v hv w hw
    have hle' : Subgroup.closure (Set.range e) ≤ Subgroup.centralizer ({v} : Set Q) :=
      (Subgroup.closure_le _).2 (by
        rintro _ ⟨i, rfl⟩
        exact Subgroup.mem_centralizer_singleton_iff.2 (hv i).eq)
    have hle : ∀ x ∈ Subgroup.closure (Set.range e), Commute x v := fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.1 (hle' hx)
    rw [Subgroup.sup_eq_closure] at hw
    induction hw using Subgroup.closure_induction with
    | mem w hw =>
      rcases hw with hw | hw
      · exact ⟨w, hw, 0, by rw [zpow_zero, mul_one]⟩
      · obtain ⟨c, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
        exact ⟨1, one_mem _, c, by rw [one_mul]⟩
    | one => exact ⟨1, one_mem _, 0, by rw [zpow_zero, mul_one]⟩
    | mul w w' _ _ ih ih' =>
      obtain ⟨x, hx, c, rfl⟩ := ih
      obtain ⟨x', hx', c', rfl⟩ := ih'
      refine ⟨x * x', mul_mem hx hx', c + c', ?_⟩
      have hcx : Commute (v ^ c) x' := ((hle x' hx').zpow_right c).symm
      rw [zpow_add]
      calc x * v ^ c * (x' * v ^ c') = x * (v ^ c * x') * v ^ c' := by group
        _ = x * (x' * v ^ c) * v ^ c' := by rw [hcx.eq]
        _ = x * x' * (v ^ c * v ^ c') := by group
    | inv w _ ih =>
      obtain ⟨x, hx, c, rfl⟩ := ih
      refine ⟨x⁻¹, inv_mem hx, -c, ?_⟩
      have hcx : Commute x (v ^ c) := (hle x hx).zpow_right c
      rw [mul_inv_rev, zpow_neg]
      exact hcx.inv_inv.eq.symm
  let S : Option (Option (Fin 4)) → Subgroup Q := fun o => o.elim
    (Subgroup.closure (Set.range e) ⊔ Subgroup.zpowers f)
    fun o' => o'.elim (Subgroup.closure (Set.range e) ⊔ Subgroup.zpowers u)
      fun i => Subgroup.centralizer ({y i} : Set Q)
  have h := three_pow_card_le_card_closure g hg S
    (by
      rintro (_ | _ | a) (_ | _ | b) hab
      · exact absurd rfl hab
      · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers f)
      · exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨b, rfl⟩)
      · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
      · exact absurd rfl hab
      · exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨b, rfl⟩)
      · exact Subgroup.mem_centralizer_singleton_iff.2 (hyu a).eq.symm
      · exact Subgroup.mem_centralizer_singleton_iff.2 (hyf a).eq.symm
      · exact Subgroup.mem_centralizer_singleton_iff.2
          (hy a b fun h => hab (h ▸ rfl)).eq.symm)
    (by
      rintro (_ | _ | a) h
      ·
        obtain ⟨x, hx, c, hxc⟩ := hdecomp f hef u h
        have hx1 : x = 1 := eq_one_of_mem_closure e x y hee he3 hy (fun i => by
          have : x = u * (f ^ c)⁻¹ := by rw [hxc]; group
          rw [this]
          exact (hyu i).mul_right ((hyf i).zpow_right c).inv_right) hyi hx
        have h1 : f ^ (-c) * u ^ (1 : ℤ) = 1 := by
          rw [hxc, hx1, one_mul, zpow_one, zpow_neg]; group
        exact absurd (hind _ _ h1).2 (by norm_num)
      ·
        obtain ⟨x, hx, c, hxc⟩ := hdecomp u heu f h
        have hx1 : x = 1 := eq_one_of_mem_closure e x y hee he3 hy (fun i => by
          have : x = f * (u ^ c)⁻¹ := by rw [hxc]; group
          rw [this]
          exact (hyf i).mul_right ((hyu i).zpow_right c).inv_right) hyi hx
        have h1 : f ^ (1 : ℤ) * u ^ (-c) = 1 := by
          rw [hxc, hx1, one_mul, zpow_one, zpow_neg]; group
        exact absurd (hind _ _ h1).1 (by norm_num)
      · exact hyi a (Subgroup.mem_centralizer_singleton_iff.1 h).symm)
    (by
      rintro (_ | _ | a)
      · exact hu3
      · exact hf3
      · exact he3 a)
  simpa using h

end Count

section Rank

theorem six_le_pRank_of_cover_of_witnesses {L Q : Type} [Group L] [Finite L] [Group Q]
    [Finite Q] (π : L →* Q) (hπ : Function.Surjective π)
    (hker : ∀ x, π x = 1 ↔ x ∈ Subgroup.center L) (hZ : 3 ∣ Nat.card (Subgroup.center L))
    (e N : Fin 4 → Q) (f M : Q) (hee : ∀ i j, Commute (e i) (e j))
    (hef : ∀ i, Commute (e i) f) (he3 : ∀ i, e i ^ 3 = 1) (hf3 : f ^ 3 = 1)
    (he1 : ∀ i, e i ≠ 1) (hf1 : f ≠ 1)
    (hNe : ∀ i, N i * e i * (N i)⁻¹ = (e i)⁻¹)
    (hNe' : ∀ i j, i ≠ j → Commute (N i) (e j)) (hNf : ∀ i, Commute (N i) f)
    (hMf : M * f * M⁻¹ = f⁻¹) :
    6 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L) := by
  set g : Option (Fin 4) → Q := fun o => o.elim f e
  set n : Option (Fin 4) → Q := fun o => o.elim M N
  have hg : ∀ i j, g i * g j = g j * g i := by
    rintro (_ | a) (_ | b)
    · rfl
    · exact (hef b).symm.eq
    · exact (hef a).eq
    · exact (hee a b).eq
  have hconj : ∀ {x y : Q}, Commute x y → x * y * x⁻¹ = y := fun h => by
    rw [h.eq, mul_inv_cancel_right]
  have hrel : ∀ i j, (∃ k : ℤ, n i * g j * (n i)⁻¹ = g j * g i ^ k) ∨
      (∃ k : ℤ, n j * g i * (n j)⁻¹ = g i * g j ^ k) := by
    rintro (_ | a) (_ | b)
    · exact .inl ⟨-2, by
        change M * f * M⁻¹ = f * f ^ (-2 : ℤ)
        rw [hMf]
        group⟩
    · exact .inr ⟨0, by
        change N b * f * (N b)⁻¹ = f * e b ^ (0 : ℤ)
        rw [zpow_zero, mul_one]
        exact hconj (hNf b)⟩
    · exact .inl ⟨0, by
        change N a * f * (N a)⁻¹ = f * e a ^ (0 : ℤ)
        rw [zpow_zero, mul_one]
        exact hconj (hNf a)⟩
    · by_cases hab : a = b
      · subst hab
        exact .inl ⟨-2, by
          change N a * e a * (N a)⁻¹ = e a * e a ^ (-2 : ℤ)
          rw [hNe]
          group⟩
      · exact .inl ⟨0, by
          change N a * e b * (N a)⁻¹ = e b * e a ^ (0 : ℤ)
          rw [zpow_zero, mul_one]
          exact hconj (hNe' a b hab)⟩
  obtain ⟨R, hR3, hRc, hRmap⟩ := exists_elemAbelian_of_reflection_lifts' π hπ
    (fun x hx => (hker x).1 hx) g n hg
    (by rintro (_ | a); exacts [hf3, he3 a])
    (by rintro (_ | a); exacts [hMf, hNe a]) hrel
  have hyi : ∀ i, ¬ Commute (N i) (e i) := by
    intro i h
    have h1 : (e i)⁻¹ = e i := by rw [← hNe i]; exact hconj h
    have h2 : e i * e i = 1 := mul_eq_one_iff_eq_inv.2 h1.symm
    have h3 : e i ^ 3 = e i * (e i * e i) := pow_three _
    rw [h2, mul_one, he3 i] at h3
    exact he1 i h3.symm
  have hbig := three_pow_five_le_card_closure e N f (fun i j => hee i j) hef he3 hf3 hf1
    hNe' hNf hyi
  rw [← hRmap] at hbig
  have := pRank_ge_of_lift π hker R hR3 hRc hZ hbig
  simpa using this

theorem six_le_pRank_of_witnesses {Q : Type} [Group Q] [Finite Q] (e y : Fin 4 → Q) (f u : Q)
    (hee : ∀ i j, Commute (e i) (e j))
    (hef : ∀ i, Commute (e i) f) (heu : ∀ i, Commute (e i) u) (hfu : Commute f u)
    (he3 : ∀ i, e i ^ 3 = 1) (hf3 : f ^ 3 = 1) (hu3 : u ^ 3 = 1)
    (hy : ∀ i j, i ≠ j → Commute (y i) (e j)) (hyf : ∀ i, Commute (y i) f)
    (hyu : ∀ i, Commute (y i) u) (hyi : ∀ i, ¬ Commute (y i) (e i))
    (hind : ∀ a c : ℤ, f ^ a * u ^ c = 1 → (3 : ℤ) ∣ a ∧ (3 : ℤ) ∣ c) :
    6 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Q) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set g : Option (Option (Fin 4)) → Q := fun o => o.elim u fun o' => o'.elim f e
  have hg : ∀ i j, Commute (g i) (g j) := by
    rintro (_ | _ | a) (_ | _ | b)
    · exact Commute.refl _
    · exact hfu.symm
    · exact (heu b).symm
    · exact hfu
    · exact Commute.refl _
    · exact (hef b).symm
    · exact heu a
    · exact hef a
    · exact hee a b
  have hE := isElemAbelian_closure g hg (by rintro (_ | _ | a); exacts [hu3, hf3, he3 a])
  have hbig := three_pow_six_le_card_closure e y f u hee hef heu hfu he3 hf3 hu3 hy hyf hyu hyi
    hind
  have hP : IsPGroup 3 (Subgroup.closure (Set.range g)) := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, hE.2 _ x.2, Subgroup.coe_one])⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (G := Subgroup.closure (Set.range g))).1 hP
  rw [hk] at hbig
  exact ((Nat.pow_le_pow_iff_right (by norm_num)).1 hbig).trans
    (le_pRank (by norm_num) le_top hE hk)

end Rank

end CFSG.HardMathSupport.Timmesfeld.Tables.T1b
