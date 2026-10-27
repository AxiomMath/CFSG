module

public import CFSG.Certificates.Kernel.ExcExt.OrbitSound

public section

namespace CFSG.ExcExtK

open CFSG.StandardType.GGQ2Frame CFSG.StandardType.GGQ2Frame.ExcRaw

variable {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat}

theorem of_orbit (hK : TabsOK m K fx hx fx' hx') (P : V m → Prop)
    (hP : ∀ (u : Root m) (v : V m), P v → P (reflection m u v)) {B : ℕ} {reps : List ℕ}
    (hB : ∀ c < 3 ^ dim m, orbOK K B reps c = true) (hR : ∀ c ∈ reps, P (vec m c)) (vx : V m) :
    P vx := by
  have key : ∀ n c, c < 3 ^ dim m → depE (ln32 B c) = n → P (vec m c) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro c hc hn
      rcases orbOK_spec (hB c hc) with hmem | ⟨hp, hu, hdp, hrefl⟩
      · exact hR c hmem
      · generalize parE (ln32 B c) = p at hp hdp hrefl
        generalize refE (ln32 B c) = u at hu hrefl
        rw [hK.hd] at hp
        rw [hK.hr] at hu
        have hpar := ih _ (lt_of_lt_of_eq hdp hn) p hp rfl
        have h2 : reflK K u p = code m (reflection m ⟨u, hu⟩ (vec m p)) := reflK_eq hK ⟨u, hu⟩ p
        have e : vec m c = reflection m ⟨u, hu⟩ (vec m p) := by
          rw [← hrefl, h2, vec_code]
        rw [e]
        exact hP _ _ hpar
  have h := key _ (code m vx) (code_lt m vx) rfl
  rwa [vec_code] at h

end CFSG.ExcExtK

end
