module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsMaxEng

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Cls

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] {τ : K →+* K}
variable {p : ℕ} {Ω : Type} [Group Ω] {S B : Subgroup Ω}
variable {H : Subgroup (GL ι K)} {β : (ι → K) →ₗ[K] (ι → K) →ₛₗ[τ] K}

private theorem eq_one_of_mem_centralizer (hZ : Subgroup.center ↥S = ⊥) {g : Ω} (hgS : g ∈ S)
    (hgC : g ∈ Subgroup.centralizer (S : Set Ω)) : g = 1 := by
  have h : (⟨g, hgS⟩ : ↥S) ∈ Subgroup.center ↥S := Subgroup.mem_center_iff.2 fun s =>
    Subtype.ext (Subgroup.mem_centralizer_iff.1 hgC s s.2)
  rw [hZ, Subgroup.mem_bot] at h
  exact congrArg Subtype.val h

theorem comm_map_theta (hSn : S.Normal) (hZ : Subgroup.center ↥S = ⊥) (hB : IsElemAbelian p B)
    (Dat : ClsInner p S B H β) {x : Ω} (hx : x ∈ B) (y : ↥(innerPart S B)) :
    x * Dat.φ (Dat.θ y) = Dat.φ (Dat.θ y) * x := by
  set s := Dat.φ (Dat.θ y) with hsdef
  have hs : s ∈ S := Dat.range_eq ▸ ⟨_, rfl⟩
  have hc : s⁻¹ * (y : Ω) ∈ Subgroup.centralizer (S : Set Ω) := Dat.θ_spec y
  have hxy : x * (y : Ω) * x⁻¹ = y := by
    rw [hB.comm hx y.2.1, mul_inv_cancel_right]
  have h1 : x * s * x⁻¹ ∈ S := hSn.conj_mem s hs x
  have h2 : x * (s⁻¹ * (y : Ω)) * x⁻¹ ∈ Subgroup.centralizer (S : Set Ω) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have hg' : x⁻¹ * g * x ∈ S := by
      simpa using hSn.conj_mem g hg x⁻¹
    have := Subgroup.mem_centralizer_iff.1 hc _ hg'
    calc g * (x * (s⁻¹ * (y : Ω)) * x⁻¹)
        = x * ((x⁻¹ * g * x) * (s⁻¹ * (y : Ω))) * x⁻¹ := by group
      _ = x * ((s⁻¹ * (y : Ω)) * (x⁻¹ * g * x)) * x⁻¹ := by rw [this]
      _ = x * (s⁻¹ * (y : Ω)) * x⁻¹ * g := by group
  have hsplit : (x * s * x⁻¹)⁻¹ * s = (x * (s⁻¹ * (y : Ω)) * x⁻¹) * (s⁻¹ * (y : Ω))⁻¹ := by
    have e : x * (s⁻¹ * (y : Ω)) * x⁻¹ = (x * s * x⁻¹)⁻¹ * (x * (y : Ω) * x⁻¹) := by group
    rw [e, hxy]
    group
  have hmS : (x * s * x⁻¹)⁻¹ * s ∈ S := S.mul_mem (S.inv_mem h1) hs
  have hmC : (x * s * x⁻¹)⁻¹ * s ∈ Subgroup.centralizer (S : Set Ω) := by
    rw [hsplit]
    exact Subgroup.mul_mem _ h2 (Subgroup.inv_mem _ hc)
  have h3 := eq_one_of_mem_centralizer hZ hmS hmC
  have h4 : x * s * x⁻¹ = s := (inv_mul_eq_one.1 h3)
  calc x * s = x * s * x⁻¹ * x := by group
    _ = s * x := by rw [h4]

variable [Finite Ω]

theorem inf_eq_map_of_involution (hp : p.Prime) [hSn : S.Normal] (hZ : Subgroup.center ↥S = ⊥)
    (hB : IsElemAbelian p B) (hrank : p ^ GLATwoLocalRank p Ω ≤ Nat.card B)
    (Dat : ClsInner p S B H β) {z : GL ι K} (hzH : z ∈ H) (hz2 : z ^ 2 = 1)
    (hz1 : Dat.φ ⟨z, hzH⟩ ≠ 1) (hzF : z ∈ centGL (fieldSet Dat))
    (hzA : ∀ y ∈ liftGroup Dat, z * y = y * z) :
    B ⊓ S = Dat.θ.range.map Dat.φ := by
  set T : Subgroup Ω := Dat.θ.range.map Dat.φ with hTdef
  set zH : ↥H := ⟨z, hzH⟩ with hzHdef
  set t : Ω := Dat.φ zH with htdef
  have hTS : T ≤ S := by
    rw [← Dat.range_eq]
    exact Subgroup.map_le_range _ _
  have htS : t ∈ S := Dat.range_eq ▸ ⟨zH, rfl⟩
  have hBT : ∀ x ∈ B, ∀ e ∈ T, x * e = e * x := by
    rintro x hx _ ⟨_, ⟨y, rfl⟩, rfl⟩
    exact comm_map_theta hSn hZ hB Dat hx y
  have hE : IsElemAbelian p (B ⊔ T) :=
    hB.sup_of_commute (CFSG.SectionRank.isElemAbelian_map Dat.elem Dat.φ) hBT
  have hθt : ∀ y : ↥(innerPart S B), Dat.φ (Dat.θ y) * t = t * Dat.φ (Dat.θ y) := by
    intro y
    have hmem : ((Dat.θ y : ↥H) : GL ι K) ∈ liftGroup Dat := ⟨Dat.θ y, ⟨y, rfl⟩, rfl⟩
    have hc : Dat.θ y * zH = zH * Dat.θ y := Subtype.ext (hzA _ hmem).symm
    rw [htdef, ← map_mul, ← map_mul, hc]
  have hB₁ : innerPart S B ≤ Subgroup.centralizer {t} := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    set y : ↥(innerPart S B) := ⟨x, hx⟩
    have hc : (Dat.φ (Dat.θ y))⁻¹ * x ∈ Subgroup.centralizer (S : Set Ω) := Dat.θ_spec y
    have hct := Subgroup.mem_centralizer_iff.1 hc t htS
    calc x * t = Dat.φ (Dat.θ y) * ((Dat.φ (Dat.θ y))⁻¹ * x) * t := by group
      _ = Dat.φ (Dat.θ y) * (t * ((Dat.φ (Dat.θ y))⁻¹ * x)) := by rw [mul_assoc, ← hct]
      _ = (Dat.φ (Dat.θ y) * t) * ((Dat.φ (Dat.θ y))⁻¹ * x) := by group
      _ = t * x := by rw [hθt y]; group
  have hBc : B ≤ Subgroup.centralizer {t} := by
    rcases Dat.split with h | hF
    · exact h ▸ hB₁
    · obtain ⟨hbB, -, hBb, -, hact, -, -⟩ := id hF
      rw [hBb]
      refine sup_le hB₁ ?_
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      have hse : ModelGen.semiConj Dat.A Dat.σ z = z :=
        semiConj_eq_of_comm fun v => (mem_centGL.mp hzF) _ ⟨hF, rfl⟩ v
      obtain ⟨k', hk', hφk'⟩ := hact.2.2 zH
      have hke : k' = zH := Subtype.ext (hk'.trans hse)
      rw [hke] at hφk'
      calc Dat.b * t = Dat.b * t * Dat.b⁻¹ * Dat.b := by group
        _ = t * Dat.b := by rw [htdef, ← hφk']
  have hTc : T ≤ Subgroup.centralizer {t} := by
    rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.2 (hθt y)
  have hEt : ∀ e ∈ B ⊔ T, e * t = t * e := fun e he =>
    Subgroup.mem_centralizer_singleton_iff.1 (sup_le hBc hTc he)
  have ht2 : t ^ 2 = 1 := by
    rw [htdef, ← map_pow]
    have : zH ^ 2 = 1 := Subtype.ext (by simpa [hzHdef] using hz2)
    rw [this, map_one]
  have hle := ModelGen.card_le_card_of_involution hp hrank hE hz1 ht2 hEt
  have hBE : B = B ⊔ T := Subgroup.eq_of_le_of_card_ge le_sup_left hle
  have hTB : T ≤ B := by
    rw [hBE]
    exact le_sup_right
  refine le_antisymm ?_ (le_inf hTB hTS)
  rintro x ⟨hxB, hxS⟩
  have hx1 : x ∈ innerPart S B := ⟨hxB, Subgroup.mem_sup_left hxS⟩
  set y : ↥(innerPart S B) := ⟨x, hx1⟩
  have hc : (Dat.φ (Dat.θ y))⁻¹ * x ∈ Subgroup.centralizer (S : Set Ω) := Dat.θ_spec y
  have hcS : (Dat.φ (Dat.θ y))⁻¹ * x ∈ S :=
    S.mul_mem (S.inv_mem (hTS ⟨_, ⟨y, rfl⟩, rfl⟩)) hxS
  have h1 := eq_one_of_mem_centralizer hZ hcS hc
  have hx : x = Dat.φ (Dat.θ y) := (inv_mul_eq_one.1 h1).symm
  rw [hx]
  exact ⟨_, ⟨y, rfl⟩, rfl⟩

theorem innerPart_eq_sup_of_involution (hp : p.Prime) [hSn : S.Normal]
    (hcore : GLAPPrimeCore p ↥S = ⊥) (hZ : Subgroup.center ↥S = ⊥) (hB : IsElemAbelian p B)
    (hrank : p ^ GLATwoLocalRank p Ω ≤ Nat.card B) (Dat : ClsInner p S B H β) {z : GL ι K}
    (hzH : z ∈ H) (hz2 : z ^ 2 = 1) (hz1 : Dat.φ ⟨z, hzH⟩ ≠ 1)
    (hzF : z ∈ centGL (fieldSet Dat)) (hzA : ∀ y ∈ liftGroup Dat, z * y = y * z) :
    innerPart S B = (B ⊓ centModSubgroup p S) ⊔ (B ⊓ S) ∧
      (B ⊓ centModSubgroup p S) ⊓ (B ⊓ S) = ⊥ ∧ Nat.card ↥(B ⊓ S) = Nat.card Dat.θ.range := by
  have hT := inf_eq_map_of_involution hp hZ hB hrank Dat hzH hz2 hz1 hzF hzA
  have h0 : B ⊓ centModSubgroup p S = B ⊓ Subgroup.centralizer (S : Set Ω) :=
    ModelGen.inf_centMod_eq_inf_centralizer hSn hcore
  refine ⟨le_antisymm ?_ ?_, ?_, ?_⟩
  · intro x hx
    set y : ↥(innerPart S B) := ⟨x, hx⟩
    have hs : Dat.φ (Dat.θ y) ∈ B ⊓ S := hT ▸ ⟨_, ⟨y, rfl⟩, rfl⟩
    have hc : (Dat.φ (Dat.θ y))⁻¹ * x ∈ B ⊓ centModSubgroup p S := by
      rw [h0]
      exact ⟨B.mul_mem (B.inv_mem hs.1) hx.1, Dat.θ_spec y⟩
    have e : x = (Dat.φ (Dat.θ y))⁻¹ * x * Dat.φ (Dat.θ y) := by
      rw [hB.comm (B.mul_mem (B.inv_mem hs.1) hx.1) hs.1]
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right hs)
  · refine sup_le ?_ ?_
    · rw [h0]
      exact inf_le_inf_left _ le_sup_right
    · exact inf_le_inf_left _ le_sup_left
  · rw [eq_bot_iff, h0]
    rintro x ⟨⟨-, hxc⟩, -, hxS⟩
    exact Subgroup.mem_bot.2 (eq_one_of_mem_centralizer hZ hxS hxc)
  · rw [hT]
    have hres : Function.Injective (Dat.φ.domRestrict Dat.θ.range) := by
      refine (injective_iff_map_eq_one _).2 fun x hx => ?_
      have hk : (x : ↥H) ∈ Dat.θ.range ⊓ Dat.φ.ker := ⟨x.2, hx⟩
      rw [Dat.range_inf_ker, Subgroup.mem_bot] at hk
      exact Subtype.ext hk
    rw [← MonoidHom.domRestrict_range]
    exact (Nat.card_congr (MonoidHom.ofInjective hres).toEquiv).symm

end CFSG.LocalAnalysis.GLTheoremA.S267.Cls
