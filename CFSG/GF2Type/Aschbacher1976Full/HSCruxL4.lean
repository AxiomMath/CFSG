module

public import CFSG.GF2Type.Aschbacher1976Full.HSCruxBasic
public import CFSG.GF2Type.Aschbacher1976Full.HSBadLocal2

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS

open CFSG CFSG.Blueprint Subgroup PartC

variable {G : Type} [Group G] [Finite G]

theorem mem_E_or_kE {z k : G} {E : Subgroup G} (hE : IsCruxE z k E) (hk : k ∈ Fz z)
    (hk2 : k * k ∈ E) {f : G} (hf : f ∈ Fz z) : f ∈ E ∨ k⁻¹ * f ∈ E := by
  obtain ⟨-, hEn, -, -, hFE, -⟩ := hE
  have hFH : Fz z ≤ Hz z := Subgroup.map_subtype_le _
  have hkH : k ∈ Hz z := hFH hk
  have hn : ∀ x ∈ E, k⁻¹ * x * k ∈ E := fun x hx => by
    have := hEn k⁻¹ ((Hz z).inv_mem hkH) x hx
    rwa [inv_inv] at this
  let U : Subgroup G :=
    { carrier := {x | x ∈ E ∨ k⁻¹ * x ∈ E}
      one_mem' := Or.inl E.one_mem
      mul_mem' := fun {x y} hx hy => by
        rcases hx with hx | hx <;> rcases hy with hy | hy
        · exact Or.inl (E.mul_mem hx hy)
        · right
          have : k⁻¹ * (x * y) = (k⁻¹ * x * k) * (k⁻¹ * y) := by group
          rw [this]
          exact E.mul_mem (hn x hx) hy
        · right
          have : k⁻¹ * (x * y) = (k⁻¹ * x) * y := by group
          rw [this]
          exact E.mul_mem hx hy
        · left
          have : x * y = (k * k) * (k⁻¹ * (k⁻¹ * x) * k) * (k⁻¹ * y) := by group
          rw [this]
          exact E.mul_mem (E.mul_mem hk2 (hn _ hx)) hy
      inv_mem' := fun {x} hx => by
        rcases hx with hx | hx
        · exact Or.inl (E.inv_mem hx)
        · right
          have : k⁻¹ * x⁻¹ = (k⁻¹ * (x⁻¹ * k) * k) * (k * k)⁻¹ := by group
          rw [this]
          refine E.mul_mem (hn _ ?_) (E.inv_mem hk2)
          have h' := E.inv_mem hx
          rwa [mul_inv_rev, inv_inv] at h' }
  have hkU : k ∈ U := Or.inr (by simp)
  have hEU : E ≤ U := fun x hx => Or.inl hx
  have hle : Subgroup.zpowers k ⊔ E ≤ U := sup_le (Subgroup.zpowers_le.mpr hkU) hEU
  exact hle (hFE hf)

theorem inv_conj_mem {z k : G} {E : Subgroup G} (hE : IsCruxE z k E) (hk : k ∈ Fz z)
    (hk2 : k * k ∈ E) {h f : G} (hh : h ∈ Hz z) (hf : f ∈ Fz z) :
    f⁻¹ * (h * f * h⁻¹) ∈ E := by
  have hE' := hE
  obtain ⟨-, hEn, -, hkE, -, -⟩ := hE'
  rcases mem_E_or_kE hE hk hk2 hf with hfE | hfE
  · exact E.mul_mem (E.inv_mem hfE) (hEn h hh f hfE)
  · have hkh : h * k * h⁻¹ ∈ Fz z := Width.Fz_conj_mem hh hk
    have hkhE : k⁻¹ * (h * k * h⁻¹) ∈ E := by
      rcases mem_E_or_kE hE hk hk2 hkh with h1 | h1
      · exact absurd (by
          have := hEn h⁻¹ ((Hz z).inv_mem hh) _ h1
          rwa [show h⁻¹ * (h * k * h⁻¹) * h⁻¹⁻¹ = k by group] at this) hkE
      · exact h1
    set e := k⁻¹ * f with he
    have hfe : f = k * e := by rw [he]; group
    have : f⁻¹ * (h * f * h⁻¹) = e⁻¹ * (k⁻¹ * (h * k * h⁻¹)) * (h * e * h⁻¹) := by
      rw [hfe]; group
    rw [this]
    exact E.mul_mem (E.mul_mem (E.inv_mem hfE) hkhE) (hEn h hh e hfE)

theorem cruxL4_holds :
    ∀ {G : Type} [Group G] [Finite G] {z : G}, HSSetting G z → HSTI z → FibreProp z →
      ∀ k : G, ZF z = Subgroup.zpowers k → ∀ E : Subgroup G, IsCruxE z k E →
        ∀ u ∈ Dinv z, ∀ y : G, ZF u = Subgroup.zpowers y → ∀ h : ↥(Hz z),
          qmk z h * yBar z u * (qmk z h)⁻¹ = yBar z u → y⁻¹ * ((h : G) * y * (h : G)⁻¹) ∈ E := by
  intro G _ _ z hset hti hfib k hk E hE u hu y hy h hh
  obtain ⟨⟨_, _, hz, hsymp⟩, hZ4⟩ := hset
  have hF2 : IsPGroup 2 ↥(Fz z) := hsymp.1
  obtain ⟨Z, A, hD⟩ := Width.exists_Z4Data hZ4
  have hE' := hE
  obtain ⟨-, hEn, hzE, hkE, -, hDE⟩ := hE'
  obtain ⟨hk4, hk2⟩ := gen_props hD hz hF2 (IsConj.refl z) hk
  have hkF : k ∈ Fz z := by
    rw [← hD.sup_eq]
    exact Subgroup.mem_sup_left (by rw [← ZF_z hD hz hF2]; exact hk ▸ mem_zpowers k)
  have hkkE : k * k ∈ E := by rw [← pow_two, hk2]; exact hzE
  obtain ⟨hy4, hy2⟩ := gen_props hD hz hF2 hu.1 hy
  have huE : u ∈ E := hDE hu
  obtain ⟨-, -, -, hu2, hu1⟩ := ZF_props hD hz hF2 hu.1
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right (by rwa [← pow_two])
  have hyy : y * y = u := by rw [← pow_two, hy2]
  have hyyi : y⁻¹ * y⁻¹ = u := by
    rw [← mul_inv_rev, hyy, hui]
  have hv : (h : G) * u * (h : G)⁻¹ ∈ Dinv z := Dinv_conj hu h.2
  have hyb : yBar z ((h : G) * u * (h : G)⁻¹) = yBar z u := by
    rw [yBar_conj hD hz hF2 hti hu h]
    exact hh
  have hPG : IsPGroup 2 ↥(Subgroup.closure ({yBar z u, yBar z ((h : G) * u * (h : G)⁻¹)} :
      Set (Qbar z))) := by
    rw [hyb, Set.pair_eq_singleton, ← Subgroup.zpowers_eq_closure]
    exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_yBar hD hz hF2 hti hu]; norm_num)
  have hgen : ZF ((h : G) * u * (h : G)⁻¹) = zpowers ((h : G) * y * (h : G)⁻¹) :=
    ZF_conj_zpowers (h : G) hy
  have hmem : (h : G) * y * (h : G)⁻¹ ∈ ZF ((h : G) * u * (h : G)⁻¹) := hgen ▸ mem_zpowers _
  have hord : orderOf ((h : G) * y * (h : G)⁻¹) = 4 := by
    have := Bad.orderOf_conj_inv y (h : G)⁻¹
    rwa [inv_inv, hy4] at this
  rcases hfib u hu _ hv hPG with h1 | h1
  ·
    rw [h1, hy] at hmem
    rcases Bad.eq_or_eq_inv_of_mem_zpowers hy4 hord hmem with h2 | h2
    · rw [h2]; simpa using E.one_mem
    · rw [h2, hyyi]; exact huE
  ·
    obtain ⟨a, haF, ha⟩ := exists_conj_mul_z' hD hz ((hti.2 u hu).1) hu1 hu.2.1
      (by rw [← pow_two]; exact hu2)
    have hay : ZF (u * z) = zpowers (a⁻¹ * y * a) := by
      have := ZF_conj_zpowers a⁻¹ hy
      rwa [inv_inv, ha] at this
    rw [h1, hay] at hmem
    have hord' : orderOf (a⁻¹ * y * a) = 4 := by
      have := Bad.orderOf_conj_inv y a
      rwa [hy4] at this
    have hFH : Fz z ≤ Hz z := Subgroup.map_subtype_le _
    have hyH : y ∈ Hz z := hu.2.2 (hy ▸ mem_zpowers y)
    have key : y⁻¹ * (a⁻¹ * y * a) ∈ E := by
      have h1' := inv_conj_mem hE hkF hkkE ((Hz z).inv_mem hyH) haF
      have := E.inv_mem h1'
      rw [mul_inv_rev, inv_inv] at this
      convert this using 1
      group
    rcases Bad.eq_or_eq_inv_of_mem_zpowers hord' hord hmem with h2 | h2
    · rw [h2]; exact key
    · rw [h2]
      have e1 : y⁻¹ * (a⁻¹ * y * a)⁻¹ = (y⁻¹ * (a⁻¹ * y * a)) * (a⁻¹ * (y⁻¹ * y⁻¹) * a) := by
        group
      have e2 : a⁻¹ * (y⁻¹ * y⁻¹) * a = u * z := by
        rw [hyyi, ← ha]
      rw [e1, e2]
      exact E.mul_mem key (E.mul_mem huE hzE)

end CFSG.GF2Type.Aschbacher1976Full.HS
