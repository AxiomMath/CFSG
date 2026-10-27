module

public import CFSG.GroupTheory.ThompsonAxB
public import CFSG.GH74.Uniqueness.Section132W
public import CFSG.GH74.Uniqueness.Section13A

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem A6.exists_commutator_decomp {G : Type*} [Group G] [Finite G] {T N : Subgroup G}
    (hNc : ∀ m ∈ N, ∀ s ∈ T, m * s = s * m) {a : G}
    (haT : ∀ s ∈ T, a * s * a⁻¹ ∈ T) (haN : ∀ m ∈ N, a * m = m * a)
    (hfpf : ∀ s ∈ T, a * s * a⁻¹ * s⁻¹ ∈ N → s ∈ N) :
    ∀ s ∈ T, ∃ s' ∈ T, ∃ m ∈ N, s = (a * s' * a⁻¹ * s'⁻¹) * m := by
  classical
  set N' : Subgroup ↥T := N.subgroupOf T with hN'
  let f : ↥T → ↥T := fun s => ⟨a * s * a⁻¹ * s⁻¹, T.mul_mem (haT s s.2) (T.inv_mem s.2)⟩
  have hf : ∀ s s' : ↥T, ((f s : G))⁻¹ * (f s' : G) =
      (s : G) * (a * ((s : G)⁻¹ * (s' : G)) * a⁻¹ * ((s : G)⁻¹ * (s' : G))⁻¹) * (s : G)⁻¹ :=
    fun s s' => by
      change (a * (s : G) * a⁻¹ * (s : G)⁻¹)⁻¹ * (a * s' * a⁻¹ * (s' : G)⁻¹) = _
      group
  have hwd : ∀ s s' : ↥T, s⁻¹ * s' ∈ N' → (f s)⁻¹ * f s' ∈ N' := by
    intro s s' h
    have h' : (s : G)⁻¹ * (s' : G) ∈ N := h
    change (((f s)⁻¹ * f s' : ↥T) : G) ∈ N
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hf]
    have e1 : a * ((s : G)⁻¹ * s') * a⁻¹ * ((s : G)⁻¹ * s')⁻¹ = 1 := by
      rw [haN _ h']
      group
    rw [e1, mul_one, mul_inv_cancel]
    exact N.one_mem
  have hinj : ∀ s s' : ↥T, (f s)⁻¹ * f s' ∈ N' → s⁻¹ * s' ∈ N' := by
    intro s s' h
    have h' : (((f s)⁻¹ * f s' : ↥T) : G) ∈ N := h
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hf] at h'
    set r : G := (s : G)⁻¹ * s' with hr
    have hrT : r ∈ T := T.mul_mem (T.inv_mem s.2) s'.2
    have hcomm : a * r * a⁻¹ * r⁻¹ ∈ N := by
      have e3 : a * r * a⁻¹ * r⁻¹ = (s : G)⁻¹ * ((s : G) * (a * r * a⁻¹ * r⁻¹) * (s : G)⁻¹) * s := by
        group
      rw [e3]
      have h4 : (s : G)⁻¹ * ((s : G) * (a * r * a⁻¹ * r⁻¹) * (s : G)⁻¹) * s =
          (s : G) * (a * r * a⁻¹ * r⁻¹) * (s : G)⁻¹ := by
        have := hNc _ h' (s : G) s.2
        calc (s : G)⁻¹ * ((s : G) * (a * r * a⁻¹ * r⁻¹) * (s : G)⁻¹) * s
            = (s : G)⁻¹ * (((s : G) * (a * r * a⁻¹ * r⁻¹) * (s : G)⁻¹) * s) := by group
          _ = (s : G)⁻¹ * ((s : G) * ((s : G) * (a * r * a⁻¹ * r⁻¹) * (s : G)⁻¹)) := by rw [this]
          _ = (s : G) * (a * r * a⁻¹ * r⁻¹) * (s : G)⁻¹ := by group
      rw [h4]
      exact h'
    exact hfpf r hrT hcomm
  let g : ↥T ⧸ N' → ↥T ⧸ N' := Quotient.lift (fun s => (QuotientGroup.mk (f s) : ↥T ⧸ N'))
    (fun s s' hss' => QuotientGroup.eq.mpr (hwd s s' (QuotientGroup.leftRel_apply.mp hss')))
  have hg : ∀ s : ↥T, g (QuotientGroup.mk s) = QuotientGroup.mk (f s) := fun s => rfl
  have hginj : Function.Injective g := by
    intro q₁ q₂ h
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective q₁
    obtain ⟨s', rfl⟩ := QuotientGroup.mk_surjective q₂
    rw [hg, hg] at h
    exact QuotientGroup.eq.mpr (hinj s s' (QuotientGroup.eq.mp h))
  have hgsurj := Finite.injective_iff_surjective.mp hginj
  intro s hs
  obtain ⟨q, hq⟩ := hgsurj (QuotientGroup.mk ⟨s, hs⟩)
  obtain ⟨s', rfl⟩ := QuotientGroup.mk_surjective q
  rw [hg] at hq
  set m₀ : ↥T := (f s')⁻¹ * ⟨s, hs⟩ with hm₀
  have h1 : m₀ ∈ N' := QuotientGroup.eq.mp hq
  refine ⟨s', s'.2, (m₀ : G), h1, ?_⟩
  change s = (f s' : G) * ((f s' : G)⁻¹ * s)
  rw [mul_inv_cancel_left]

theorem A6.axb {G : Type*} [Group G] [Finite G] {P R B : Subgroup G} (hP : IsPGroup 2 P)
    (hR : Odd (Nat.card R)) (hB : IsPGroup 2 B) (hRP : ∀ r ∈ R, ∀ x ∈ P, r * x * r⁻¹ ∈ P)
    (hBP : ∀ b ∈ B, ∀ x ∈ P, b * x * b⁻¹ ∈ P) (hRB : ∀ r ∈ R, ∀ b ∈ B, r * b = b * r)
    (hfix : ∀ x ∈ P, (∀ b ∈ B, b * x = x * b) → ∀ r ∈ R, r * x = x * r) :
    ∀ r ∈ R, ∀ x ∈ P, r * x = x * r := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : ∀ K : Subgroup G, (∀ k ∈ K, ∀ x ∈ P, k * x * k⁻¹ ∈ P) → K ≤ normalizer (P : Set G) := by
    intro K hK k hk
    rw [mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hK k hk x hx, fun hx => ?_⟩
    have := hK k⁻¹ (K.inv_mem hk) _ hx
    simpa [mul_assoc] using this
  have hRN := hN R hRP
  have hBN := hN B hBP
  let α : R →* MulAut P := P.normalizerMonoidHom.comp (Subgroup.inclusion hRN)
  let β : B →* MulAut P := P.normalizerMonoidHom.comp (Subgroup.inclusion hBN)
  have hα : ∀ (r : R) (x : P), ((α r x : P) : G) = r * x * (r : G)⁻¹ := fun r x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe P (Subgroup.inclusion hRN r) x
  have hβ : ∀ (b : B) (x : P), ((β b x : P) : G) = b * x * (b : G)⁻¹ := fun b x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe P (Subgroup.inclusion hBN b) x
  have hcomm : ∀ r b, α r * β b = β b * α r := by
    intro r b
    refine MulEquiv.ext fun x => Subtype.ext ?_
    have hrb : (r : G) * b = b * r := hRB r r.2 b b.2
    rw [MulAut.mul_apply, MulAut.mul_apply, hα, hβ, hβ, hα]
    calc (r : G) * (b * x * (b : G)⁻¹) * (r : G)⁻¹ = (r * b) * x * ((r : G) * b)⁻¹ := by group
      _ = (b * r) * x * ((b : G) * r)⁻¹ := by rw [hrb]
      _ = b * (r * x * (r : G)⁻¹) * (b : G)⁻¹ := by group
  have hfix' : ∀ r x, (∀ b, β b x = x) → α r x = x := by
    intro r x hx
    have hxB : ∀ b ∈ B, b * (x : G) = x * b := by
      intro b hb
      have h := congrArg Subtype.val (hx ⟨b, hb⟩)
      rw [hβ] at h
      calc b * (x : G) = b * x * b⁻¹ * b := by group
        _ = x * b := by rw [h]
    have hrx := hfix x x.2 hxB r r.2
    apply Subtype.ext
    rw [hα, hrx, mul_inv_cancel_right]
  have hR' : ¬ 2 ∣ Nat.card R := hR.not_two_dvd_nat
  have key := CFSG.GroupTheory.thompson_A_times_B hP hR' hB α β hcomm hfix'
  intro r hr x hx
  have h := congrArg (fun f : MulAut P => ((f ⟨x, hx⟩ : P) : G)) (key ⟨r, hr⟩)
  simp only [hα, MulAut.one_apply] at h
  calc r * x = r * x * r⁻¹ * r := by group
    _ = x * r := by rw [h]

omit [Finite X] in
theorem A6.mem_normalizer_centralizer {A K : Subgroup X} (hK : ∀ g ∈ K, ∀ a ∈ A, g * a * g⁻¹ ∈ A)
    {g : X} (hg : g ∈ K) : g ∈ normalizer (centralizer (A : Set X) : Set X) := by
  have key : ∀ k ∈ K, ∀ x ∈ centralizer (A : Set X), k * x * k⁻¹ ∈ centralizer (A : Set X) := by
    intro k hk x hx
    rw [mem_centralizer_iff] at hx ⊢
    intro a ha
    have h1 : k⁻¹ * a * k ∈ A := by simpa using hK k⁻¹ (K.inv_mem hk) a ha
    have h2 := hx _ h1
    calc a * (k * x * k⁻¹) = k * ((k⁻¹ * a * k) * x) * k⁻¹ := by group
      _ = k * (x * (k⁻¹ * a * k)) * k⁻¹ := by rw [h2]
      _ = k * x * k⁻¹ * a := by group
  rw [mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key g hg x hx, fun hx => ?_⟩
  have := key g⁻¹ (K.inv_mem hg) _ hx
  simpa [mul_assoc] using this

theorem A6.lemma134
    (S : ZDSetup X Z M) {c : Ctx12 Z M} {n e e' : ℕ} (hL : LData c n 1) {u : X}
    {T : Subgroup X}
    {Tb : Sylow 2 (↥(cenHull Z u) ⧸ center ↥(cenHull Z u))}
    (hDu : A6.Dict Z M (cenHull Z u) n e Tb T) (hLu : c.L ≤ cenHull Z u) {A H : Subgroup X}
    (hA : A6.AData Z M (cenHull Z u) c (hLu c.t_mem_L) Tb A H) {V : Subgroup X}
    {Vb : Sylow 2 (↥(zHull Z (centralizer (A : Set X))) ⧸ center ↥(zHull Z (centralizer (A : Set X))))}
    (hDA : A6.Dict Z M (zHull Z (centralizer (A : Set X))) n e' Vb V) {U : Subgroup X}
    (hUV : U ≤ V) (hUc : ∀ v ∈ U, ∀ w ∈ U, v * w = w * v) (hMU : zHull Z M ≤ U)
    (hUsq : ∀ w ∈ U, w * w ∈ zHull Z M) (hUinv : ∀ w ∈ U, u * w * u⁻¹ = w⁻¹)
    (hUH : ∀ h ∈ M, h ∈ normalizer (zHull Z (centralizer (A : Set X)) : Set X) → h * u = u * h →
      ∀ w ∈ U, h * w * h⁻¹ ∈ U) :
    ∀ s ∈ T, ∀ w ∈ U, s * w = w * s := by
  set Lu := cenHull Z u with hLudef
  set LA := zHull Z (centralizer (A : Set X)) with hLAdef
  have hZ := S.invariant
  have hMF : zHull Z M ≤ Lu := hL.m_le.trans hLu
  have hMT := hDu.zHull_le S hL hMF
  obtain ⟨a₀, ha₀A, ha₀F, ha₀D, ha₀1⟩ := hA.exists_ne
  have hAM : ∀ a ∈ A, ∀ m ∈ zHull Z M, a * m = m * a := fun a ha m hm =>
    hA.comm_L a ha m (hL.m_le hm)
  have hAF : A ≤ Lu := hA.le_H.trans hA.H_le_F
  have hzM : c.z ∈ zHull Z M := Cor713.mem_zHull_of_mem c.hz c.hzM
  have hCM : ∀ g : X, g * c.z = c.z * g → g ∈ M := fun g hg =>
    S.prodDisc.centralizer_le_of_mem c.hz c.hzM (mem_centralizer_singleton_iff.mpr hg)
  have hHT : ∀ h ∈ H, ∀ s ∈ T, h * s * h⁻¹ ∈ T := by
    intro h hh s hs
    have hhF := hA.H_le_F hh
    have hhM := hA.H_le_M hh
    obtain ⟨k, hk⟩ := hDu.two hs
    exact hDu.mem_of_mem_M S (M.mul_mem (M.mul_mem hhM (hDu.le_M S hs)) (M.inv_mem hhM))
      (Lu.mul_mem (Lu.mul_mem hhF (hDu.le hs)) (Lu.inv_mem hhF)) (k := k)
      (by rw [conj_pow, hk]; group)
  have hAT : ∀ a ∈ A, ∀ s ∈ T, a * s * a⁻¹ ∈ T := fun a ha => hHT a (hA.le_H ha)
  have hfpf : ∀ s ∈ T, a₀ * s * a₀⁻¹ * s⁻¹ ∈ zHull Z M → s ∈ zHull Z M := fun s hs h =>
    hDu.fpf S hL hMF (hLu c.t_mem_L) c.ht c.htM ha₀F ha₀D ha₀1 hs h
  have hMc : ∀ m ∈ zHull Z M, ∀ s ∈ T, m * s = s * m := fun m hm s hs =>
    hDu.comm_of_mem_zHull S hL hMF hm hs
  have hdec := A6.exists_commutator_decomp hMc (hAT a₀ ha₀A) (hAM a₀ ha₀A) hfpf
  have hUA : ∀ w ∈ U, ∀ a ∈ A, a * w = w * a := fun w hw a ha =>
    mem_centralizer_iff.mp (Cor713.zHull_le _ (hDA.le (hUV hw))) a ha
  have hUM : ∀ w ∈ U, w ∈ M := fun w hw => hDA.le_M S (hUV hw)
  have hconjC : ∀ y ∈ U, ∀ s ∈ T, (y * s * y⁻¹) * u = u * (y * s * y⁻¹) ∧
      ∀ m ∈ zHull Z M, m * (y * s * y⁻¹) = (y * s * y⁻¹) * m := by
    intro y hy s hs
    have hsu : u * s = s * u := mul_comm_of_mem_cenHull (hDu.le hs)
    have hyu : u * y * u⁻¹ = y⁻¹ := hUinv y hy
    have hyu' : u * y⁻¹ * u⁻¹ = y := by
      have := congrArg (·⁻¹) hyu
      simpa [mul_assoc] using this
    have hsu' : u * s * u⁻¹ = s := by rw [hsu, mul_inv_cancel_right]
    have hsyy : s * (y * y) = (y * y) * s := (hMc _ (hUsq y hy) s hs).symm
    refine ⟨?_, fun m hm => ?_⟩
    · calc (y * s * y⁻¹) * u = y⁻¹ * ((y * y) * s) * y⁻¹ * u := by group
        _ = y⁻¹ * (s * (y * y)) * y⁻¹ * u := by rw [hsyy]
        _ = y⁻¹ * s * y * u := by group
        _ = (u * y * u⁻¹) * (u * s * u⁻¹) * (u * y⁻¹ * u⁻¹) * u := by rw [hyu, hsu', hyu']
        _ = u * (y * s * y⁻¹) := by group
    · have h1 : y⁻¹ * m * y ∈ zHull Z M := hL.sec126_conj_mem_zHull (hUM y hy) hm
      have h2 := hMc _ h1 s hs
      calc m * (y * s * y⁻¹) = y * ((y⁻¹ * m * y) * s) * y⁻¹ := by group
        _ = y * (s * (y⁻¹ * m * y)) * y⁻¹ := by rw [h2]
        _ = (y * s * y⁻¹) * m := by group
  have hUT : ∀ y ∈ U, ∀ s ∈ T, y * s * y⁻¹ ∈ T := by
    intro y hy s hs
    obtain ⟨k, hk⟩ := hDu.two hs
    obtain ⟨s', hs', m, hm, hsdec⟩ := hdec s hs
    set c' := y * s' * y⁻¹ with hc'
    obtain ⟨hcu, hcM⟩ := hconjC y hy s' hs'
    have hcN : c' ∈ normalizer (Lu : Set X) :=
      A6.mem_normalizer_zHull hZ (le_normalizer (mem_centralizer_singleton_iff.mpr hcu))
    have hya : y * a₀ = a₀ * y := (hUA y hy a₀ ha₀A).symm
    have e1 : y * s * y⁻¹ = (a₀ * (c' * a₀⁻¹ * c'⁻¹)) * (y * m * y⁻¹) := by
      rw [hsdec, hc']
      calc y * (a₀ * s' * a₀⁻¹ * s'⁻¹ * m) * y⁻¹
          = (y * a₀) * s' * (a₀⁻¹ * s'⁻¹ * m) * y⁻¹ := by group
        _ = (a₀ * y) * s' * (a₀⁻¹ * s'⁻¹ * m) * y⁻¹ := by rw [hya]
        _ = a₀ * (y * s') * a₀⁻¹ * s'⁻¹ * m * y⁻¹ := by group
        _ = a₀ * (y * s') * (a₀⁻¹ * y⁻¹) * (y * s'⁻¹ * y⁻¹) * (y * m * y⁻¹) := by group
        _ = a₀ * (y * s') * (y⁻¹ * a₀⁻¹) * (y * s'⁻¹ * y⁻¹) * (y * m * y⁻¹) := by
            rw [show a₀⁻¹ * y⁻¹ = y⁻¹ * a₀⁻¹ from by
              rw [← mul_inv_rev, ← mul_inv_rev, hya]]
        _ = (a₀ * ((y * s' * y⁻¹) * a₀⁻¹ * (y * s' * y⁻¹)⁻¹)) * (y * m * y⁻¹) := by group
    have hc1 : c' * a₀⁻¹ * c'⁻¹ ∈ Lu := (mem_normalizer_iff.mp hcN _).mp (Lu.inv_mem (hAF ha₀A))
    have hLu1 : a₀ * (c' * a₀⁻¹ * c'⁻¹) ∈ Lu := Lu.mul_mem (hAF ha₀A) hc1
    have hcz : c' * c.z = c.z * c' := (hcM c.z hzM).symm
    have haz : a₀ * c.z = c.z * a₀ := hAM a₀ ha₀A c.z hzM
    have hM1 : a₀ * (c' * a₀⁻¹ * c'⁻¹) ∈ M := by
      refine hCM _ ?_
      have haz' : a₀⁻¹ * c.z = c.z * a₀⁻¹ := by
        calc a₀⁻¹ * c.z = a₀⁻¹ * (c.z * a₀) * a₀⁻¹ := by group
          _ = a₀⁻¹ * (a₀ * c.z) * a₀⁻¹ := by rw [haz]
          _ = c.z * a₀⁻¹ := by group
      have hcz' : c'⁻¹ * c.z = c.z * c'⁻¹ := by
        calc c'⁻¹ * c.z = c'⁻¹ * (c.z * c') * c'⁻¹ := by group
          _ = c'⁻¹ * (c' * c.z) * c'⁻¹ := by rw [hcz]
          _ = c.z * c'⁻¹ := by group
      calc a₀ * (c' * a₀⁻¹ * c'⁻¹) * c.z = a₀ * c' * a₀⁻¹ * (c'⁻¹ * c.z) := by group
        _ = a₀ * c' * (a₀⁻¹ * c.z) * c'⁻¹ := by rw [hcz']; group
        _ = a₀ * (c' * c.z) * a₀⁻¹ * c'⁻¹ := by rw [haz']; group
        _ = (a₀ * c.z) * c' * a₀⁻¹ * c'⁻¹ := by rw [hcz]; group
        _ = c.z * (a₀ * (c' * a₀⁻¹ * c'⁻¹)) := by rw [haz]; group
    have hym : y * m * y⁻¹ ∈ zHull Z M := hL.m_normal y (hUM y hy) m hm
    have hM' : y * s * y⁻¹ ∈ M := by
      rw [e1]
      exact M.mul_mem hM1 (Cor713.zHull_le M hym)
    have hLu' : y * s * y⁻¹ ∈ Lu := by
      rw [e1]
      exact Lu.mul_mem hLu1 (hMF hym)
    exact hDu.mem_of_mem_M S hM' hLu' (k := k) (by rw [conj_pow, hk]; group)
  have hAB : ∃ s ∈ T, (∀ w ∈ U, w * s = s * w) ∧ ∃ a ∈ A, a * s ≠ s * a := by
    by_contra hcon'
    have hcon : ∀ x ∈ T, (∀ b ∈ U, b * x = x * b) → ∀ a ∈ A, a * x = x * a := by
      intro x hx hxU a ha
      by_contra hne
      exact hcon' ⟨x, hx, hxU, a, ha, hne⟩
    have hTp : IsPGroup 2 T := hDu.isP
    have hUp : IsPGroup 2 U := hDA.isP.to_le hUV
    have hcent := A6.axb hTp hA.odd hUp hAT hUT (fun a ha w hw => (hUA w hw a ha))
      (fun x hx hxU a ha => hcon x hx hxU a ha)
    have hTM : T ≤ zHull Z M := fun s hs => hfpf s hs (by
      rw [hcent a₀ ha₀A s hs, mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _)
    have h1 := Subgroup.card_le_of_le hTM
    rw [hDu.card_eq, hL.m_card] at h1
    have h2 : 2 ^ n < (2 ^ n) ^ 3 := by
      have h4 : 4 ≤ 2 ^ n := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hL.hn
      have := pow_lt_pow_right₀ (show 1 < 2 ^ n by omega) (show 1 < 3 by norm_num)
      simpa using this
    omega
  obtain ⟨s, hs, hsU, a, ha, has⟩ := hAB
  set W := T ⊓ centralizer (U : Set X) with hW
  have hMW : zHull Z M ≤ W := fun m hm =>
    mem_inf.mpr ⟨hMT hm, mem_centralizer_iff.mpr fun w hw => hUc w hw m (hMU hm)⟩
  have hHN : ∀ h ∈ H, h ∈ normalizer (LA : Set X) := fun h hh =>
    A6.mem_normalizer_zHull hZ (A6.mem_normalizer_centralizer hA.norm hh)
  have hHu : ∀ h ∈ H, h * u = u * h := fun h hh =>
    (mul_comm_of_mem_cenHull (hA.H_le_F hh)).symm
  have hHW : ∀ h ∈ H, ∀ w ∈ W, h * w * h⁻¹ ∈ W := by
    intro h hh w hw
    obtain ⟨hwT, hwC⟩ := mem_inf.mp hw
    refine mem_inf.mpr ⟨hHT h hh w hwT, mem_centralizer_iff.mpr fun v hv => ?_⟩
    have hh' : h⁻¹ ∈ H := inv_mem hh
    have hvU : h⁻¹ * v * h⁻¹⁻¹ ∈ U :=
      hUH h⁻¹ (hA.H_le_M hh') (hHN h⁻¹ hh') (hHu h⁻¹ hh') v hv
    rw [inv_inv] at hvU
    have h1 := mem_centralizer_iff.mp hwC _ hvU
    calc v * (h * w * h⁻¹) = h * ((h⁻¹ * v * h) * w) * h⁻¹ := by group
      _ = h * (w * (h⁻¹ * v * h)) * h⁻¹ := by rw [h1]
      _ = (h * w * h⁻¹) * v := by group
  rcases hDu.irred S hL hMF (hLu c.t_mem_L) c.ht c.htM hA.surj hMW inf_le_left hHW with h1 | h1
  · exfalso
    apply has
    have hsW : s ∈ W := mem_inf.mpr ⟨hs, mem_centralizer_iff.mpr fun w hw => hsU w hw⟩
    rw [h1] at hsW
    exact hAM a ha s hsW
  · intro s' hs' w hw
    have hs'W : s' ∈ W := h1 ▸ hs'
    exact (mem_centralizer_iff.mp (mem_inf.mp hs'W).2 w hw).symm

end CFSG.GH74.Uniqueness
