module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.T1b

open CFSG.Open

section Count

variable {G M : Type*} [CommGroup G] [Finite G] [Group M]

theorem card_ker_pow_le_card_map_mul (g : G →* M) :
    Nat.card (powMonoidHom 3 : G →* G).ker ≤
      Nat.card ((powMonoidHom 3 : G →* G).ker.map g) * Nat.card g.ker := by
  set K3 := (powMonoidHom 3 : G →* G).ker with hK3
  have h := Subgroup.card_ker_mul_card_range (g.comp K3.subtype)
  have hrange : (g.comp K3.subtype).range = K3.map g := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hle : (g.comp K3.subtype).ker ≤ g.ker.subgroupOf K3 := fun x hx => by
    simpa [MonoidHom.mem_ker, Subgroup.mem_subgroupOf] using hx
  have hcard : Nat.card (g.comp K3.subtype).ker ≤ Nat.card g.ker := by
    calc Nat.card (g.comp K3.subtype).ker ≤ Nat.card (g.ker.subgroupOf K3) :=
          Nat.card_mono (Set.toFinite _) hle
      _ ≤ Nat.card g.ker :=
          Nat.card_le_card_of_injective (fun x => ⟨(x : G), x.2⟩) (fun a b h => by
            have h' := congrArg Subtype.val h
            exact Subtype.ext (Subtype.ext h'))
  rw [hrange] at h
  rw [← h, mul_comm (Nat.card (K3.map g))]
  exact Nat.mul_le_mul_right _ hcard

theorem exists_elemAbelian_of_cube_kernel (g : G →* M) (hZ : ∀ z ∈ g.ker, ∃ y : G, y ^ 3 = z) :
    ∃ E : Subgroup M, IsElemAbelian 3 E ∧
      Nat.card E = Nat.card (powMonoidHom 3 : G →* G).ker := by
  set κ : G →* G := powMonoidHom 3 with hκ
  set A : Subgroup G := g.ker.comap κ with hA
  have hcube : ∀ x : G, κ x = x ^ 3 := fun x => rfl
  have hker_A : g.ker ≤ A := fun c hc => by
    show κ c ∈ g.ker
    rw [hcube, MonoidHom.mem_ker, map_pow, (MonoidHom.mem_ker).1 hc, one_pow]
  have hkκ_A : κ.ker ≤ A := fun c hc => by
    show κ c ∈ g.ker
    rw [(MonoidHom.mem_ker).1 hc]
    exact one_mem _
  refine ⟨A.map g, ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩, ?_⟩
  · obtain ⟨x, -, hx⟩ := Subgroup.mem_map.1 a.2
    obtain ⟨z, -, hz⟩ := Subgroup.mem_map.1 b.2
    apply Subtype.ext
    change (a : M) * b = b * a
    rw [← hx, ← hz, ← map_mul, ← map_mul, mul_comm]
  · obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    rw [← map_pow]
    have : κ x ∈ g.ker := hx
    rwa [hcube, MonoidHom.mem_ker] at this
  ·
    set θ : A →* G := κ.comp A.subtype with hθ
    have hθrange : θ.range = g.ker := by
      ext z
      constructor
      · rintro ⟨x, rfl⟩
        exact x.2
      · intro hz
        obtain ⟨y, hy⟩ := hZ z hz
        refine ⟨⟨y, ?_⟩, ?_⟩
        · show κ y ∈ g.ker
          rw [hcube, hy]; exact hz
        · change κ y = z
          rw [hcube, hy]
    have hθker : Nat.card θ.ker = Nat.card κ.ker := by
      have : θ.ker = κ.ker.subgroupOf A := by
        ext x; simp [hθ, MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      rw [this]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkκ_A).toEquiv
    have h1 := Subgroup.card_ker_mul_card_range θ
    rw [hθker, hθrange] at h1
    set h : A →* M := g.comp A.subtype with hh
    have hrange : h.range = A.map g := by
      rw [hh, MonoidHom.range_comp, Subgroup.range_subtype]
    have hker : Nat.card h.ker = Nat.card g.ker := by
      have : h.ker = g.ker.subgroupOf A := by
        ext x; simp [hh, MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      rw [this]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker_A).toEquiv
    have h2 := Subgroup.card_ker_mul_card_range h
    rw [hker, hrange] at h2
    have hpos : 0 < Nat.card g.ker := Nat.card_pos
    have : Nat.card g.ker * Nat.card (A.map g) = Nat.card g.ker * Nat.card κ.ker := by
      rw [h2, mul_comm, h1]
    exact Nat.eq_of_mul_eq_mul_left hpos this

end Count

theorem exists_cube_of_pow_eq_one {C : Type*} [CommGroup C] [Finite C] [IsCyclic C]
    (h9 : 9 ∣ Nat.card C) {x : C} (hx : x ^ 3 = 1) : ∃ y : C, y ^ 3 = x := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := C)
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg x)
  have hord : orderOf g = Nat.card C := orderOf_eq_card_of_forall_mem_zpowers hg
  have h1 : g ^ (m * 3) = 1 := by rw [zpow_mul, zpow_ofNat]; exact hx
  have h2 : (orderOf g : ℤ) ∣ m * 3 := orderOf_dvd_iff_zpow_eq_one.2 h1
  rw [hord] at h2
  have h9' : (9 : ℤ) ∣ (Nat.card C : ℤ) := by exact_mod_cast h9
  have h3 : (9 : ℤ) ∣ m * 3 := h9'.trans h2
  obtain ⟨k, hk⟩ : (3 : ℤ) ∣ m := by omega
  refine ⟨g ^ k, ?_⟩
  rw [← zpow_natCast, ← zpow_mul, hk, mul_comm]
  norm_num

end CFSG.HardMathSupport.Timmesfeld.Tables.T1b
